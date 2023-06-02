/*   FILE: ConfigManager.java
 *   DATE OF CREATION:   Thu Jan 09 14:14:35 2003
 *   Copyright (c) Emmanuel Pietriga, 2002. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 *   $Id: ConfigManager.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Color;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.event.ActionListener;
import java.awt.event.ActionEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.awt.Font;
import java.awt.GridLayout;
import java.awt.BorderLayout;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.Vector;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.ListSelectionModel;
import javax.swing.event.ListSelectionListener;
import javax.swing.event.ListSelectionEvent;


import fr.inria.zvtm.engine.SwingWorker;
import fr.inria.zvtm.engine.Location;

import org.apache.xerces.dom.DOMImplementationImpl;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class ConfigManager {

    public static final String zgrvURI = "http://zvtm.sourceforge.net/zgrviewer";

    static final String MAIN_TITLE = "ZGRViewer";

    static int mainViewW=800;
    static int mainViewH=600;
    static int mainViewX=0;
    static int mainViewY=0;

    static int rdW = 300;
    static int rdH = 200;

    static Font defaultFont = new Font("Dialog", 0, 12);
    static Font SMALL_FONT = new Font("Dialog", 0, 10);

    static final String _BLANK = "_blank";
    static final String _SELF = "_self";

    static Font PIEMENU_FONT = defaultFont;

    Color backgroundColor = Color.WHITE;
    static Color HIGHLIGHT_COLOR = Color.RED;

    public static Color OBSERVED_REGION_COLOR = new Color(186,135,186);
    public static Color OBSERVED_REGION_BORDER_COLOR = Color.getHSBColor(0.83519f,0.28f,0.45f); //rgb(299,28,45)
    public static Color OBSERVED_REGION_CROSSHAIR_COLOR = new Color(115, 83, 115);
    static {
        if (!(Utils.osIsWindows() || Utils.osIsMacOS())){
            OBSERVED_REGION_BORDER_COLOR = OBSERVED_REGION_CROSSHAIR_COLOR = Color.RED;
        }
    }

    public static Color PIEMENU_FILL_COLOR = Color.BLACK;
    public static Color PIEMENU_BORDER_COLOR = Color.WHITE;
    public static Color PIEMENU_INSIDE_COLOR = Color.DARK_GRAY;
    public static final float PIEMENU_MAIN_ALPHA = 0.85f;
    public static final float PIEMENU_SUB_ALPHA = 0.95f;


    /* Misc. Prefs */
    static boolean SAVE_WINDOW_LAYOUT=false;
    static boolean DELETE_TEMP_FILES=true;
    static boolean ANTIALIASING=false;
    static boolean DYNASPOT=false;
    /*add -q option in command line args, forcing dot/neato to remain silent
      (do not issue warnings or errors that cause Java's runtime exec never to terminate)*/
    static boolean FORCE_SILENT = true;

    static String CMD_LINE_OPTS="";

    //directories
    static File m_TmpDir;
    public static File m_PrjDir=new File("graphs");
    static File m_DotPath=new File("dot");
    static File m_NeatoPath=new File("neato");
    static File m_CircoPath = new File("circo");
    static File m_TwopiPath = new File("twopi");
    static File m_GraphVizFontDir = new File("");
    public static File m_LastDir=null;
    static File m_LastExportDir=null;
    /*Plug in directory*/
    public static File plugInDir=new File("plugins");
    Plugin[] plugins;
    private Hashtable tmpPluginSettings;

    File lastFileOpened = null;

    /*location of the configuration file - at init time, we look for it in the user's home dir.
     If it is not there, we take the one in ZGRViewer dir.*/
    static String PREFS_FILE_NAME = ".zgrviewer";
    static String OLD_PREFS_FILE_NAME = "zgrviewer.cfg";

    public static final int ANIM_MOVE_LENGTH = 300;

    /*magnification factor when centering on a glyph - 1.0 (default) means that
      the glyph will occupy the whole screen. mFactor < 1 will make the glyph
      smaller (zoom out). mFactor > 1 will make the glyph appear bigger (zoom in)*/
    public static float MAG_FACTOR = .5f;

    /*External (platform-dependant) browser*/
    //a class to access a platform-specific web browser (not initialized at startup, but only on demand)
    static WebBrowser webBrowser;
    //try to automatically detect browser (do not take browser path into account)
    static boolean autoDetectBrowser=true;
    //path to the browser's exec file
    static File browserPath=new File("");
    //browser command line options
    static String browserOptions="";

    /*proxy/firewall configuration*/
    static boolean useProxy=false;
    static String proxyHost="";    //proxy hostname
    static String proxyPort="80";    //default value for the JVM proxyPort system property

    /*speed-dependant autozoom data*/
    double SD_ZOOM_THRESHOLD = 300;
    boolean SD_ZOOM_ENABLED = false;
    //default factor is 2
    double autoZoomFactor = 1;
    double autoUnzoomFactor = -0.5;

    static Vector LAST_COMMANDS;
    static int COMMAND_LIMIT = 5;

    GraphicsManager grMngr;

    ConfigManager(GraphicsManager gm, boolean applet){
        this.grMngr = gm;
        LAST_COMMANDS = new Vector();
        if (!applet){m_TmpDir = new File(System.getProperty("java.io.tmpdir"));}
    }

    /* load user prefs from config file (in theory, if the file cannot be found,
       every variable should have a default value) */
    void loadConfig(){
        File cfgFile = new File(System.getProperty("user.home") + File.separatorChar + PREFS_FILE_NAME);
        if (!cfgFile.exists()){
            cfgFile = new File(System.getProperty("user.home") + File.separatorChar + OLD_PREFS_FILE_NAME);
        }
        if (cfgFile.exists()){
            System.out.println("Loading Preferences from : "+cfgFile.getAbsolutePath());
            try {
                Document d=Utils.parse(cfgFile,false);
                d.normalize();
                Element rt=d.getDocumentElement();
                Element e=(Element)(rt.getElementsByTagNameNS(ConfigManager.zgrvURI,"directories")).item(0);
                try {
                    ConfigManager.m_TmpDir=new File(e.getElementsByTagNameNS(ConfigManager.zgrvURI,"tmpDir").item(0).getFirstChild().getNodeValue());
                    ConfigManager.DELETE_TEMP_FILES=(new Boolean(((Element)e.getElementsByTagNameNS(ConfigManager.zgrvURI,"tmpDir").item(0)).getAttribute("value"))).booleanValue();
                }
                catch (Exception ex){}
                try {ConfigManager.m_PrjDir=new File(e.getElementsByTagNameNS(ConfigManager.zgrvURI,"graphDir").item(0).getFirstChild().getNodeValue());}
                catch (Exception ex){}
                try {ConfigManager.m_DotPath=new File(e.getElementsByTagNameNS(ConfigManager.zgrvURI,"dot").item(0).getFirstChild().getNodeValue());}
                catch (Exception ex){}
                try {ConfigManager.m_NeatoPath=new File(e.getElementsByTagNameNS(ConfigManager.zgrvURI,"neato").item(0).getFirstChild().getNodeValue());}
                catch (Exception ex){}
                try {ConfigManager.m_CircoPath=new File(e.getElementsByTagNameNS(ConfigManager.zgrvURI,"circo").item(0).getFirstChild().getNodeValue());}
                catch (Exception ex){}
                try {ConfigManager.m_TwopiPath=new File(e.getElementsByTagNameNS(ConfigManager.zgrvURI,"twopi").item(0).getFirstChild().getNodeValue());}
                catch (Exception ex){}
                try {ConfigManager.m_GraphVizFontDir=new File(e.getElementsByTagNameNS(ConfigManager.zgrvURI,"graphvizFontDir").item(0).getFirstChild().getNodeValue());}
                catch (Exception ex){}
                //web browser settings
                try {
                    e=(Element)(rt.getElementsByTagNameNS(ConfigManager.zgrvURI,"webBrowser")).item(0);
                    ConfigManager.autoDetectBrowser=(new Boolean(e.getAttribute("autoDetect"))).booleanValue();
                    ConfigManager.browserPath=new File(e.getAttribute("path"));
                    ConfigManager.browserOptions=e.getAttribute("options");
                }
                catch (Exception ex){}
                //proxy settings
                try {
                    e=(Element)(rt.getElementsByTagNameNS(ConfigManager.zgrvURI,"proxy")).item(0);
                    updateProxy((new Boolean(e.getAttribute("enable"))).booleanValue(),
                        e.getAttribute("host"),e.getAttribute("port"));
                }
                catch (Exception ex){System.getProperties().put("proxySet","false");}
                //misc prefs
                try {
                    e=(Element)(rt.getElementsByTagNameNS(ConfigManager.zgrvURI,"preferences")).item(0);
                }
                catch (Exception ex){}
                try {
                    ConfigManager.ANTIALIASING=((new Boolean(e.getAttribute("antialiasing"))).booleanValue());
                }
                catch (Exception ex){}
                try {
                    ConfigManager.DYNASPOT=((new Boolean(e.getAttribute("dynaspot"))).booleanValue());
                }
                catch (Exception ex){}
                try {
                    ConfigManager.HIGHLIGHT_COLOR = new Color((new Integer(e.getAttribute("highlightColor"))).intValue());
                }
                catch (Exception ex){}
                try {
                    ConfigManager.SAVE_WINDOW_LAYOUT=(new Boolean(e.getAttribute("saveWindowLayout"))).booleanValue();
                }
                catch (Exception ex){}
                try {
                    this.setSDZoomEnabled((new Boolean(e.getAttribute("sdZoom"))).booleanValue());
                }
                catch (Exception ex){}
                try {
                    this.setSDZoomFactor(Integer.parseInt(e.getAttribute("sdZoomFactor")));
                }
                catch (Exception ex){}
                try {
                    this.setMagnificationFactor(Float.parseFloat(e.getAttribute("magFactor")));
                }
                catch (Exception ex){}
                try {
                    ConfigManager.CMD_LINE_OPTS=e.getAttribute("cmdL_options");
                }
                catch (Exception ex){}
                try {
                    ConfigManager.FORCE_SILENT = ((new Boolean(e.getAttribute("silent"))).booleanValue());
                }
                catch (Exception ex){}
                try {
                    if (ConfigManager.SAVE_WINDOW_LAYOUT){
                        //window layout preferences
                        e=(Element)(rt.getElementsByTagNameNS(ConfigManager.zgrvURI,"windows")).item(0);
                        mainViewX=(new Integer(e.getAttribute("mainX"))).intValue();
                        mainViewY=(new Integer(e.getAttribute("mainY"))).intValue();
                        mainViewW=(new Integer(e.getAttribute("mainW"))).intValue();
                        mainViewH=(new Integer(e.getAttribute("mainH"))).intValue();
                    }
                }
                catch (Exception ex){}
                //plugin settings
                try {
                    e = (Element)(rt.getElementsByTagNameNS(ConfigManager.zgrvURI, "plugins")).item(0);
                    if (e!=null){
                        loadPluginPreferences(e);
                    }
                }
                catch (Exception ex){System.err.println("Failed to set some plugin preferences");}
                // stored command lines (for programs other than dot/neato)
                LAST_COMMANDS.removeAllElements();
                try {
                    NodeList nl = ((Element)(rt.getElementsByTagNameNS(ConfigManager.zgrvURI, "commandLines")).item(0)).getElementsByTagNameNS(ConfigManager.zgrvURI, "li");
                    for (int i=0;i<nl.getLength();i++){
                        if (i < COMMAND_LIMIT){LAST_COMMANDS.add(nl.item(i).getFirstChild().getNodeValue());}
                    }
                }
                catch (NullPointerException ex1){}


            }
            catch (Exception ex){
                System.err.println("Error while loading ZGRViewer configuration file (" + cfgFile.getAbsolutePath() + "): ");
                ex.printStackTrace();
            }
        }
        else {System.out.println("No Preferences File Found in : "+System.getProperty("user.home"));}
    }

    void loadPluginPreferences(Element pluginsEL){
        NodeList nl = pluginsEL.getElementsByTagNameNS(ConfigManager.zgrvURI, "plugin");
        Element pluginEL, settingEL;
        Node txtVal;
        String pluginName, settingName, settingValue;
        Hashtable ht;
        NodeList nl2;
        tmpPluginSettings = new Hashtable();
        for (int i=0;i<nl.getLength();i++){
            pluginEL = (Element)nl.item(i);
            pluginName = pluginEL.getAttribute("name");
            ht = new Hashtable();
            nl2 = pluginEL.getElementsByTagNameNS(ConfigManager.zgrvURI, "setting");
            for (int j=0;j<nl2.getLength();j++){
                settingEL = (Element)nl2.item(j);
                try {
                    txtVal = settingEL.getFirstChild();
                    ht.put(settingEL.getAttribute("name"), (txtVal != null) ? txtVal.getNodeValue() : null);
                }
                catch (Exception ex){System.err.println("Failed to set some plugin preferences for "+pluginName);}
            }
            tmpPluginSettings.put(pluginName, ht);
        }
    }

    /*save user prefs to config file*/
    void saveConfig(){
        DOMImplementation di=new DOMImplementationImpl();
        //DocumentType dtd=di.createDocumentType("isv:config",null,"isv.dtd");
        Document cfg=di.createDocument(ConfigManager.zgrvURI,"zgrv:config",null);
        //generate the XML document
        Element rt=cfg.getDocumentElement();
        rt.setAttribute("xmlns:zgrv",ConfigManager.zgrvURI);
        //save directory preferences
        Element dirs=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:directories");
        rt.appendChild(dirs);
        Element aDir=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:tmpDir");
        aDir.appendChild(cfg.createTextNode(ConfigManager.m_TmpDir.toString()));
        aDir.setAttribute("value",String.valueOf(ConfigManager.DELETE_TEMP_FILES));
        dirs.appendChild(aDir);
        aDir=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:graphDir");
        aDir.appendChild(cfg.createTextNode(ConfigManager.m_PrjDir.toString()));
        dirs.appendChild(aDir);
        aDir=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:dot");
        aDir.appendChild(cfg.createTextNode(ConfigManager.m_DotPath.toString()));
        dirs.appendChild(aDir);
        aDir=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:neato");
        aDir.appendChild(cfg.createTextNode(ConfigManager.m_NeatoPath.toString()));
        dirs.appendChild(aDir);
        aDir = cfg.createElementNS(ConfigManager.zgrvURI, "zgrv:circo");
        aDir.appendChild(cfg.createTextNode(ConfigManager.m_CircoPath.toString()));
        dirs.appendChild(aDir);
        aDir = cfg.createElementNS(ConfigManager.zgrvURI, "zgrv:twopi");
        aDir.appendChild(cfg.createTextNode(ConfigManager.m_TwopiPath.toString()));
        dirs.appendChild(aDir);
        aDir=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:graphvizFontDir");
        aDir.appendChild(cfg.createTextNode(ConfigManager.m_GraphVizFontDir.toString()));
        dirs.appendChild(aDir);
        //web settings
        Element consts=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:webBrowser");
        consts.setAttribute("autoDetect",String.valueOf(ConfigManager.autoDetectBrowser));
        consts.setAttribute("path",ConfigManager.browserPath.toString());
        consts.setAttribute("options",ConfigManager.browserOptions);
        rt.appendChild(consts);
        consts=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:proxy");
        consts.setAttribute("enable",String.valueOf(ConfigManager.useProxy));
        consts.setAttribute("host",ConfigManager.proxyHost);
        consts.setAttribute("port",ConfigManager.proxyPort);
        rt.appendChild(consts);
        //save misc. constants
        consts=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:preferences");
        rt.appendChild(consts);
        //  consts.setAttribute("graphOrient",ConfigManager.GRAPH_ORIENTATION);
        consts.setAttribute("antialiasing",String.valueOf(ConfigManager.ANTIALIASING));
        consts.setAttribute("dynaspot",String.valueOf(ConfigManager.DYNASPOT));
        consts.setAttribute("highlightColor", Integer.toString(HIGHLIGHT_COLOR.getRGB()));
        consts.setAttribute("silent", String.valueOf(ConfigManager.FORCE_SILENT));
        consts.setAttribute("saveWindowLayout",String.valueOf(ConfigManager.SAVE_WINDOW_LAYOUT));
        consts.setAttribute("sdZoom",String.valueOf(SD_ZOOM_ENABLED));
        consts.setAttribute("sdZoomFactor",String.valueOf(this.getSDZoomFactor()));
        consts.setAttribute("magFactor", String.valueOf(this.getMagnificationFactor()));
        consts.setAttribute("cmdL_options",ConfigManager.CMD_LINE_OPTS);
        //window locations and sizes
        if (ConfigManager.SAVE_WINDOW_LAYOUT){
            //first update the values
            updateWindowVariables();
            consts=cfg.createElementNS(ConfigManager.zgrvURI,"zgrv:windows");
            consts.setAttribute("mainX",String.valueOf(mainViewX));
            consts.setAttribute("mainY",String.valueOf(mainViewY));
            consts.setAttribute("mainW",String.valueOf(mainViewW));
            consts.setAttribute("mainH",String.valueOf(mainViewH));
            rt.appendChild(consts);
        }
        Element pluginsEL = cfg.createElementNS(ConfigManager.zgrvURI, "zgrv:plugins");
        rt.appendChild(pluginsEL);
        Hashtable pluginSettings;
        Element pluginEL, settingEL;
        String settingName, settingValue;
        for (int i=0;i<plugins.length;i++){
            pluginSettings = plugins[i].savePreferences();
            if (pluginSettings != null && pluginSettings.size() > 0){
                pluginEL = cfg.createElementNS(ConfigManager.zgrvURI, "zgrv:plugin");
                pluginsEL.appendChild(pluginEL);
                pluginEL.setAttribute("name", plugins[i].getName());
                for (Enumeration e=pluginSettings.keys();e.hasMoreElements();){
                    settingName = (String)e.nextElement();
                    settingValue = (String)pluginSettings.get(settingName);
                    settingEL = cfg.createElementNS(ConfigManager.zgrvURI, "zgrv:setting");
                    settingEL.setAttribute("name", settingName);
                    settingEL.appendChild(cfg.createTextNode(settingValue));
                    pluginEL.appendChild(settingEL);
                }
            }
        }
        // command lines
        consts = cfg.createElementNS(ConfigManager.zgrvURI, "zgrv:commandLines");
        rt.appendChild(consts);
        if (LAST_COMMANDS != null){
            for (int i=0;i<LAST_COMMANDS.size();i++){
                Element aCommand = cfg.createElementNS(ConfigManager.zgrvURI, "zgrv:li");
                aCommand.appendChild(cfg.createTextNode((String)LAST_COMMANDS.elementAt(i)));
                consts.appendChild(aCommand);
            }
        }
        File cfgFile = new File(System.getProperty("user.home") + File.separatorChar + PREFS_FILE_NAME);
        if (cfgFile.exists()){cfgFile.delete();}
        Utils.serialize(cfg, cfgFile);
    }

    /*save command lines on exit, without modifying user settings if he did not ask to do so*/
    void saveCommandLines(){
        try {
            Document d;
            Element rt;
            Element cLines;
            File cfgFile = new File(System.getProperty("user.home") + File.separatorChar + PREFS_FILE_NAME);
            if (!cfgFile.exists()){
                cfgFile = new File(System.getProperty("user.home") + File.separatorChar + OLD_PREFS_FILE_NAME);
            }
            if (cfgFile.exists()){
                d = Utils.parse(cfgFile, false);
                d.normalize();
                rt = d.getDocumentElement();
                if ((rt.getElementsByTagNameNS(ConfigManager.zgrvURI, "commandLines")).getLength()>0){
                    rt.removeChild((rt.getElementsByTagNameNS(ConfigManager.zgrvURI, "commandLines")).item(0));
                }
                cLines = d.createElementNS(ConfigManager.zgrvURI, "zgrv:commandLines");
                if (LAST_COMMANDS != null){
                    for (int i=0;i<LAST_COMMANDS.size();i++){
                        Element aCmdLine = d.createElementNS(ConfigManager.zgrvURI, "zgrv:li");
                        aCmdLine.appendChild(d.createTextNode((String)LAST_COMMANDS.elementAt(i)));
                        cLines.appendChild(aCmdLine);
                    }
                }
            }
            else {
                DOMImplementation di = new DOMImplementationImpl();
                d = di.createDocument(ConfigManager.zgrvURI, "zgrv:config", null);
                rt = d.getDocumentElement();
                rt.setAttribute("xmlns:zgrv", ConfigManager.zgrvURI);
                cLines = d.createElementNS(ConfigManager.zgrvURI, "zgrv:commandLines");
                if (LAST_COMMANDS != null){
                    for (int i=0;i<LAST_COMMANDS.size();i++){
                        Element aCmdLine = d.createElementNS(ConfigManager.zgrvURI, "zgrv:li");
                        aCmdLine.appendChild(d.createTextNode((String)LAST_COMMANDS.elementAt(i)));
                        cLines.appendChild(aCmdLine);
                    }
                }
            }
            rt.appendChild(cLines);
            cfgFile = new File(System.getProperty("user.home") + File.separatorChar + PREFS_FILE_NAME);
            Utils.serialize(d, cfgFile);
        }
        catch (Exception ex){}
    }

    static boolean checkProgram(short prg){
        switch (prg){
            case DOTManager.DOT_PROGRAM:{return (m_TmpDir.exists() && ConfigManager.m_DotPath.exists());}
            case DOTManager.NEATO_PROGRAM:{return (m_TmpDir.exists() && ConfigManager.m_NeatoPath.exists());}
            case DOTManager.TWOPI_PROGRAM:{return (m_TmpDir.exists() && ConfigManager.m_TwopiPath.exists());}
            case DOTManager.CIRCO_PROGRAM:{return (m_TmpDir.exists() && ConfigManager.m_CircoPath.exists());}
            default:{return false;}
        }
    }

    static String getDirStatus(){
        StringBuffer sb=new StringBuffer();
        sb.append("Temp Directory (required): ");
        sb.append((m_TmpDir.exists()) ? m_TmpDir.toString() : Messages.PATH_NOT_SET);
        sb.append("\n");
        sb.append("Absolute Path to dot (required if using dot): ");
        sb.append((m_DotPath.exists()) ? m_DotPath.toString() : Messages.PATH_NOT_SET);
        sb.append("\n");
        sb.append("Absolute Path to neato (required if using neato): ");
        sb.append((m_NeatoPath.exists()) ? m_NeatoPath.toString() : Messages.PATH_NOT_SET);
        sb.append("\n");
        sb.append("Absolute Path to circo (required if using circo): ");
        sb.append((m_CircoPath.exists()) ? m_CircoPath.toString() : Messages.PATH_NOT_SET);
        sb.append("\n");
        sb.append("Absolute Path to twopi (required if using twopi): ");
        sb.append((m_TwopiPath.exists()) ? m_TwopiPath.toString() : Messages.PATH_NOT_SET);
        sb.append("\n");
        sb.append("GraphViz Font Directory (optional): ");
        sb.append((m_GraphVizFontDir.exists()) ? m_GraphVizFontDir.toString() : Messages.PATH_NOT_SET);
        sb.append("\n");
        sb.append("Are you sure you want to continue?");
        return sb.toString();
    }

    /*update window position and size variables prior to saving them in the config file*/
    void updateWindowVariables(){
        mainViewX = grMngr.mainView.getFrame().getX();
        mainViewY = grMngr.mainView.getFrame().getY();
        mainViewW = grMngr.mainView.getFrame().getWidth();
        mainViewH = grMngr.mainView.getFrame().getHeight();
    }

    /*set speed-dependent automatic zooming*/
    public void setSDZoomEnabled(boolean b){
        SD_ZOOM_ENABLED = b;
    }

    /*speed-dependent automatic zooming status*/
    public boolean isSDZoomEnabled(){
        return SD_ZOOM_ENABLED;
    }

    /*amount of autozoom ; f belongs to [2.0, 10.0] <- values allowed by Pref window slider*/
    public void setSDZoomFactor(double f){
        autoZoomFactor = f - 1;
        autoUnzoomFactor = (1 - f) / f;
    }

    /*amount of autozoom ; res belongs to [2.0, 10.0]*/
    public int getSDZoomFactor(){
        return (int)autoZoomFactor + 1;
    }

    /*threshold beyond which autozooming is triggered (usually a percentage of the View's size in pixels)*/
    public void setSDZoomThreshold(double t){
        SD_ZOOM_THRESHOLD = t;
    }

    public double getSDZoomThreshold(){
        return SD_ZOOM_THRESHOLD;
    }

    public void setMagnificationFactor(float f){
        MAG_FACTOR = f;
    }

    public float getMagnificationFactor(){
        return MAG_FACTOR;
    }

    /*remember command lines input in CallBox*/
    void rememberCommandLine(String cmdLine){
        boolean exists = false;
        for (int i=0;i<LAST_COMMANDS.size();i++){
            if (((String)LAST_COMMANDS.elementAt(i)).equals(cmdLine)){
                if (i > 0){
                    String tmp = (String)LAST_COMMANDS.firstElement();
                    LAST_COMMANDS.setElementAt(cmdLine, 0);
                    LAST_COMMANDS.setElementAt(tmp, i);
                }
                return;
            }
        }
        LAST_COMMANDS.insertElementAt(cmdLine, 0);
        if (LAST_COMMANDS.size() > COMMAND_LIMIT){LAST_COMMANDS.removeElementAt(COMMAND_LIMIT);}  //we limit the list to COMMAND_LIMIT elements
    }

    /*could also be set at runtime from command line
      java -DproxySet=true -DproxyHost=proxy_host -DproxyPort=proxy_port*/
    static void updateProxy(boolean use,String hostname,String port){
        ConfigManager.useProxy=use;
        ConfigManager.proxyHost=hostname;
        ConfigManager.proxyPort=port;
        if (ConfigManager.useProxy){
            System.getProperties().put("proxySet","true");
            System.getProperties().put("proxyHost",ConfigManager.proxyHost);
            System.getProperties().put("proxyPort",ConfigManager.proxyPort);
        }
        else {
            System.getProperties().put("proxySet","false");
        }
    }

    /* ------------------------ Plugins ----------------------------- */

    static File[] pluginJARs = null;

    static void setPlugInJARs(String[] list){
        pluginJARs = new File[list.length];
        for (int i=0;i<list.length;i++){
            pluginJARs[i] = new File(list[i]);
        }
    }

    protected void initPlugins(ZGRViewer application){
        Vector plgs = new Vector();
        //list all files in 'plugins' dir
        if (pluginJARs == null){
            pluginJARs = ConfigManager.plugInDir.listFiles();
        }
        if (pluginJARs != null && pluginJARs.length>0){
            URL[] urls = new URL[pluginJARs.length];
            //store path to each JAR file in plugins dir as a URL so that they can be added
            //later dynamically to the classpath (through a new ClassLoader)
            for (int i=0;i<pluginJARs.length;i++){
                try {
                    // going through URI and then URL as advised in JDK 1.6
                    urls[i] = pluginJARs[i].toURI().toURL();
                }
                catch(MalformedURLException mue){System.err.println("Failed to instantiate a class loader for plug-ins: "+mue);}
            }
            //instantiate a new class loader with a classpath containing all JAR files in plugins directory
            URLClassLoader ucl = new URLClassLoader(urls);
            JarFile jf;
            String s;
            Plugin plgInstance = null;
            //for each of these JAR files
            for (int i=0;i<pluginJARs.length;i++){
                try {
                    jf = new JarFile(pluginJARs[i]);
                    //get all CLASS entries
                    for (Enumeration e=jf.entries();e.hasMoreElements();){
                        s = ((JarEntry)e.nextElement()).getName();
                        if (s.endsWith(".class")){
                            //replace directory / by package .
                            s = Utils.replaceString(s,"/",".");
                            //get rid of .class at the end of the jar entry
                            s = s.substring(0,s.length()-6);
                            try {
                                //for each class entry, get the Class definition
                                Class c = ucl.loadClass(s);
                                Class[] interfaces = c.getInterfaces();
                                try {
                                    //find out if it implements Plugin (if it does, instantiate and store it)
                                    for (int j = 0;j<interfaces.length;j++){
                                        if (interfaces[j].getName().equals("net.claribole.zgrviewer.Plugin")){
                                            plgInstance = (Plugin)c.newInstance();
                                            System.out.print("Loading plugin: "+plgInstance.getName()+" "+plgInstance.getVersion()+"... ");
                                            plgInstance.setApplication(application);
                                            plgs.add(plgInstance);
                                            System.out.println("OK");
                                        }
                                    }
                                    plgInstance = null;
                                }
                                catch (InstantiationException ie) {
                                    System.err.println("Unable to create plug-in object for class "+
                                        s + ": " + ie.getMessage());
                                    ie.printStackTrace();
                                }
                                catch (IllegalAccessException ie) {
                                    System.err.println("Unable to create plug-in object for class "+
                                        s + ": " + ie.getMessage());
                                    ie.printStackTrace();
                                }
                            }
                            catch (ClassNotFoundException ex){System.err.println("Failed to load plug-in class "+s);}
                        }
                    }
                }
                catch (IOException ex2){System.err.println("Failed to load plug-in from JAR file "+pluginJARs[i].getAbsolutePath());}
                catch (NoClassDefFoundError ex2){System.err.println("One or more plugins might have failed to initialize because of the following error:\nNo Class Definition Found for "+ex2.getMessage());}
                catch (ClassFormatError ex2){System.err.println("One or more plugins might have failed to initialize because of the following error:\nClass Format Error for "+ex2.getMessage());}
            }
        }
        //store the plugins in arrays instead of vectors
        plugins = new Plugin[plgs.size()];
        for (int i=0;i<plgs.size();i++){
            plugins[i] = (Plugin)plgs.elementAt(i);
            try {
                plugins[i].loadPreferences((Hashtable)tmpPluginSettings.get(plugins[i].getName()));
            }
            catch (NullPointerException ex){}
        }
    }

    // event should be one of Plugin.NOTIFY_PLUGIN_*;
    void notifyPlugins(short event){
        if (plugins == null){return;}
        for (int i=0;i<plugins.length;i++){
            plugins[i].eventOccured(event);
        }
    }

    void terminatePlugins(){
        if (plugins == null){return;}
        for (int i=0;i<plugins.length;i++){
            plugins[i].terminate();
        }
    }

    void showPluginInfo(){
        StringBuffer info = new StringBuffer();
        for (int i=0;i<plugins.length;i++){
            info.append(plugins[i].getName()
                        +"\nVersion: "+plugins[i].getVersion()
                        +"\nAuthors: "+plugins[i].getAuthor()+"\n");
            if (plugins[i].getURL() != null){
                info.append("More information:" + plugins[i].getURL().toString() + "\n");
            }
            info.append("\n");
        }
        new TextViewer(info, Messages.ABOUT_PLUGINS, 0, 0, 0, 400, 300, false);
    }

    /* --------------------- Bookmarks ---------------------- */

    HashMap<String,Location> bookmarks = new HashMap(1);

    public void bookmarkCurrentLocation(BookmarksList bl){
        String bkLabel = JOptionPane.showInputDialog(bl,
                                                     "Bookmark Label:",
                                                     "Add bookmark",
                                                     JOptionPane.PLAIN_MESSAGE);
        if (bkLabel != null && bkLabel.length() > 0){
            bookmarks.put(bkLabel, grMngr.mainCamera.getLocation());
            bl.updateList();
        }
    }

    public void saveBookmarks(BookmarksList bl){
        final JFileChooser fc = new JFileChooser(ConfigManager.m_LastExportDir!=null ? ConfigManager.m_LastExportDir : ConfigManager.m_PrjDir);
        fc.setDialogTitle("Export SVG");
        int returnVal = fc.showSaveDialog(bl);
        if (returnVal == JFileChooser.APPROVE_OPTION) {
            final SwingWorker worker=new SwingWorker(){
                public Object construct(){
                    serializeBookmarks(fc.getSelectedFile());
                    return null;
                }
            };
            worker.start();
        }
    }

    void loadBookmarks(final BookmarksList bl){
        final JFileChooser fc = new JFileChooser(ConfigManager.m_LastDir!=null ? ConfigManager.m_LastDir : ConfigManager.m_PrjDir);
        fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
        fc.setDialogTitle("Find DOT File");
        int returnVal = fc.showOpenDialog(bl);
        if (returnVal == JFileChooser.APPROVE_OPTION) {
            final SwingWorker worker=new SwingWorker(){
                public Object construct(){
                    parseBookmarks(fc.getSelectedFile(), bl);
                    return null;
                }
            };
            worker.start();
        }
    }

    static final String BK_SEP = "\t";

    public void parseBookmarks(File f, BookmarksList bl){
        try {
            FileInputStream fis = new FileInputStream(f);
            BufferedReader br = new BufferedReader(new InputStreamReader(fis, "UTF-8"));
            String line = br.readLine();
            while (line != null){
                if (line.length() > 0){
                    String[] bk = line.split(BK_SEP);
                    bookmarks.put(bk[0], new Location(Double.parseDouble(bk[1]),
                                                      Double.parseDouble(bk[2]),
                                                      Double.parseDouble(bk[3])));
                }
                line = br.readLine();
            }
            fis.close();
            bl.updateList();
        }
        catch (Exception ex){System.err.println("Error while parsing bookmarks");ex.printStackTrace();}
    }

    public void serializeBookmarks(File f){
        try {
            BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(f), "UTF-8"));
            for (String label:bookmarks.keySet()){
                Location l = bookmarks.get(label);
                bw.write(label + BK_SEP +
                         String.valueOf(l.getX()) + BK_SEP +
                         String.valueOf(l.getY()) + BK_SEP +
                         String.valueOf(l.getAltitude()));
                bw.newLine();
            }
            bw.flush();
        }
        catch (Exception ex){System.err.println("Error while saving bookmarks");ex.printStackTrace();}
    }

    public void showBookmarks(){
        new BookmarksList(this);
    }

}

class BookmarksList extends JFrame implements ListSelectionListener {

    ConfigManager cm;

    JList bkList;
    JButton loadBt, saveBt, addBt;

    BookmarksList(ConfigManager cfm){
        super("Bookmark List");
        this.cm = cfm;

        Container c = this.getContentPane();

        c.setLayout(new BorderLayout());

        bkList = new JList(cm.bookmarks.keySet().toArray());
        bkList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        c.add(bkList, BorderLayout.CENTER);
        bkList.addListSelectionListener(this);

        JPanel btp = new JPanel();
        btp.setLayout(new GridLayout(1, 3));
        addBt = new JButton("Add...");
        btp.add(addBt);
        loadBt = new JButton("Load...");
        btp.add(loadBt);
        saveBt = new JButton("Save...");
        btp.add(saveBt);
        c.add(btp, BorderLayout.SOUTH);

        ActionListener a0 = new ActionListener(){
            public void actionPerformed(ActionEvent e){
                if (e.getSource() == addBt){
                    cm.bookmarkCurrentLocation(BookmarksList.this);
                }
                else if (e.getSource() == loadBt){
                    cm.loadBookmarks(BookmarksList.this);
                }
                else if (e.getSource() == saveBt){cm.saveBookmarks(BookmarksList.this);}
            }
        };
        addBt.addActionListener(a0);
        loadBt.addActionListener(a0);
        saveBt.addActionListener(a0);

        WindowListener w0 = new WindowAdapter(){
            public void windowClosing(WindowEvent e){
                dispose();
            }
         };

        addWindowListener(w0);
        setSize(400,300);
        setVisible(true);

    }

    void updateList(){
        bkList.setListData(cm.bookmarks.keySet().toArray());
        repaint();
    }

    public void valueChanged(ListSelectionEvent e){
        if (!e.getValueIsAdjusting()){
            cm.grMngr.goTo((Location)cm.bookmarks.get(bkList.getSelectedValue()));
        }
    }

}
