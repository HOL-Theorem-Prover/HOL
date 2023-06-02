/*   FILE: ZGRViewer.java
 *   DATE OF ORIGNAL CREATION:   Thu Jan 09 14:13:31 2003
 *   Copyright (c) 2003 World Wide Web Consortium. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2015. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 *   $Id: ZGRViewer.java 5325 2015-02-05 21:02:14Z epietrig $
 */

 //edited by haoyang
package net.claribole.zgrviewer;


import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.net.URL;

import javax.swing.JFileChooser;

import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.KeyStroke;

import fr.inria.zvtm.engine.SwingWorker;
import fr.inria.zvtm.engine.View;
import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.widgets.PieMenu;
import fr.inria.zvtm.widgets.PieMenuFactory;
import haoyang.FileReader;
import haoyang.TheoremParser;

import javax.swing.ImageIcon;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;

import org.apache.xerces.dom.DOMImplementationImpl;
import org.w3c.dom.Document;

import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import haoyang.UnusedSearch;

public class ZGRViewer implements ZGRApplication {

    static ConfigManager cfgMngr;
    static DOTManager dotMngr;

    public GVLoader gvLdr;
    GraphicsManager grMngr;

    static File cmdLineDOTFile=null;
    static String cmdLinePrg=null;

    //store current file
    public File[] currentFile=null;

    PieMenu mainPieMenu, subPieMenu;
    JPanel _panelView;
	ZGRGlassPane _gp;

    boolean exitVMonClose = true;

    public ZGRViewer(ZGROptions options){
        setOptions(options);
        initConfig();
        //init GUI after config as we load some GUI prefs from the config file
        initGUI(options, false);
        if (cmdLineDOTFile!=null){loadCmdLineFile();}
    }

    public ZGRViewer()
    {
    	initConfig();
        //init GUI after config as we load some GUI prefs from the config file
        initGUI(null, true);
	}

    void setOptions(ZGROptions options){
        if (options.cmdLinePrg != null){
            cmdLinePrg = options.cmdLinePrg;
        }
        if (options.gvFile != null){
            File f = new File(options.gvFile);
            if (f.exists()){cmdLineDOTFile = f;}
        }
        if (options.pluginList != null){
            //  -pluginList=<paths>        where <path> is a list of comma-separated relative
            //                             to the JAR files that contain plugins
            // takes precedence over -pluginDir
            ConfigManager.setPlugInJARs(options.pluginList.split(","));
        }
        else if (options.pluginDir != null){
            //  -pluginDir <path>          where <path> is the relative of full path to
            //                             the directory where to look for plugins
            ConfigManager.plugInDir = new File(options.pluginDir);
        }
        if (options.pluginMode != null){
            // -pluginMode <PluginClass>  plugin mode enabled by default in tool palette
            ToolPalette.setDefaultPluginMode(options.pluginMode);
        }
    }

    public void setFile(File dotFile)
    {
    	cmdLineDOTFile = dotFile;

         if (cmdLineDOTFile!=null){loadCmdLineFile();}
    }

    public GraphicsManager getGraphicsManager(){
        return grMngr;
    }

    public LogicalStructure getLogicalStructure(){
        return grMngr.lstruct;
    }

    public boolean exitVMonClose(){
        return exitVMonClose;
    }

    void loadCmdLineFile(){
        if (cmdLinePrg!=null){
            if (cmdLinePrg.equals("neato")){
            gvLdr.loadFile(cmdLineDOTFile, DOTManager.NEATO_PROGRAM, false);
            }
            else if (cmdLinePrg.equals("dot")){
            gvLdr.loadFile(cmdLineDOTFile, DOTManager.DOT_PROGRAM, false);
            }
            else if (cmdLinePrg.equals("circo")){
            gvLdr.loadFile(cmdLineDOTFile, DOTManager.CIRCO_PROGRAM, false);
            }
            else if (cmdLinePrg.equals("twopi")){
            gvLdr.loadFile(cmdLineDOTFile, DOTManager.TWOPI_PROGRAM, false);
            }
            else if (cmdLinePrg.equals("svg")){
            gvLdr.loadSVG(cmdLineDOTFile);
            }
            else {
            System.err.println("Bad option: " + cmdLinePrg + "\n\t" + Messages.CMD_LINE_ERROR);
            System.exit(0);
            }
        }
        else {
            if (cmdLineDOTFile.toString().toLowerCase().endsWith(".svg")
                || cmdLineDOTFile.toString().toLowerCase().endsWith(".svgz")){
                gvLdr.loadSVG(cmdLineDOTFile);
            }
            else {
            gvLdr.loadFile(cmdLineDOTFile, DOTManager.DOT_PROGRAM, false);
            }
        }
    }

    void initConfig(){
        grMngr = new GraphicsManager(this);
        cfgMngr = new ConfigManager(grMngr, false);
        dotMngr=new DOTManager(grMngr, cfgMngr);
        grMngr.setConfigManager(cfgMngr);
        gvLdr = new GVLoader(this, grMngr, cfgMngr, dotMngr);
        //dont load plugins
        // cfgMngr.loadConfig();
        // cfgMngr.initPlugins(this);
    }

    public ZGRGlassPane getGlassPane()
    {
    	return _gp;
	}

    void initGUI(ZGROptions options, boolean viewOnJPanel){
        boolean opengl = (options != null) ? options.opengl : false;
        exitVMonClose = !viewOnJPanel;
        cfgMngr.notifyPlugins(Plugin.NOTIFY_PLUGIN_GUI_INITIALIZING);
        Utils.initLookAndFeel();
        JMenuBar jmb = initViewMenu();
        if (viewOnJPanel)
        {
        	_panelView = grMngr.createPanelView(grMngr.createZVTMelements(true), 1080, 1080);

        	//_panelView.setLocation(ConfigManager.mainViewX,ConfigManager.mainViewY);
        	_panelView.addComponentListener(grMngr);
        	_gp = new ZGRGlassPane(grMngr);

        	grMngr.gp = _gp;

            //((JFrame)_panelView.getFrame()).setGlassPane(gp);

        }
        else
        {
        	grMngr.createFrameView(grMngr.createZVTMelements(false), opengl ? View.OPENGL_VIEW : View.STD_VIEW, jmb);
        }

        cfgMngr.notifyPlugins(Plugin.NOTIFY_PLUGIN_GUI_VIEW_CREATED);

        grMngr.parameterizeView(new ZgrvEvtHdlr(this, this.grMngr));
        
        cfgMngr.notifyPlugins(Plugin.NOTIFY_PLUGIN_GUI_INITIALIZED);

    }

    public JPanel getPanelView()
    {
    	return _panelView;
	}


    public JMenuBar initViewMenu(){
        JMenu open=new JMenu("Open");
        final JMenuItem openO = new JMenuItem("Command line...");
        final JMenuItem openDG = new JMenuItem("dot...");
        openDG.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_D, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        final JMenuItem openNG = new JMenuItem("neato...");
        openNG.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_N, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        final JMenuItem openCG = new JMenuItem("circo...");
        final JMenuItem openTG = new JMenuItem("twopi...");
        final JMenuItem openS=new JMenuItem("Open SVG generated by GraphViz...");
        final JMenuItem openDir=new JMenuItem("Open one Dir and generate a svg...");
        final JMenuItem openDirMulti=new JMenuItem("Open multi Dir and generate a svg...");
        final JMenuItem backTothy = new JMenuItem("back to last theory interface");
        final JMenuItem reloadI = new JMenuItem("Reload current file");
        reloadI.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_R, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        final JMenuItem pngI=new JMenuItem("Export to PNG (current view)...");
        final JMenuItem svgI=new JMenuItem("Export to SVG...");
        final JMenuItem printI=new JMenuItem("Print (current view)...");
        final JMenuItem exitI=new JMenuItem("Exit");
        printI.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_P, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        final JMenuItem backI=new JMenuItem("Back");
        backI.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_B,0));
        final JMenuItem globvI=new JMenuItem("Global View");
        globvI.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_G,0));
        final JMenuItem radarI=new JMenuItem("Overview");
        radarI.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_O, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        final JMenuItem showBkI = new JMenuItem("Show Bookmarks...");
        final JMenuItem searchI=new JMenuItem("Find...");
        searchI.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_F, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        final JMenuItem tagI=new JMenuItem("check tag...");
        final JMenuItem unusedI=new JMenuItem("Unused theorems...");
        
        // final JMenuItem fontI=new JMenuItem("Set Font...");
        // final JMenuItem prefsI=new JMenuItem("Preferences...");
        // final JMenuItem helpI=new JMenuItem("Commands...");
        // final JMenuItem versionI=new JMenuItem("Check for updates...");
        // final JMenuItem pluginsI = new JMenuItem("About plugins...");
        // final JMenuItem aboutI=new JMenuItem("About...");
        exitI.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_Q, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        ActionListener a0=new ActionListener(){
            public void actionPerformed(ActionEvent e){
                if (e.getSource()==openDG){gvLdr.open(DOTManager.DOT_PROGRAM, false);}
                else if (e.getSource()==openNG){gvLdr.open(DOTManager.NEATO_PROGRAM, false);}
                else if (e.getSource()==openCG){gvLdr.open(DOTManager.CIRCO_PROGRAM, false);}
                else if (e.getSource()==openTG){gvLdr.open(DOTManager.TWOPI_PROGRAM, false);}
                else if (e.getSource()==openS){gvLdr.openSVGFile();}
                else if (e.getSource()==openDir){try {
                    gvLdr.DirLoadSvg();
                } catch (IOException e1) {
                    // TODO Auto-generated catch block
                    e1.printStackTrace();
                } catch (InterruptedException e1) {
                    // TODO Auto-generated catch block
                    e1.printStackTrace();
                }}
                else if (e.getSource()==openDirMulti){try {
                    gvLdr.DirLoadSvg_multi();
                } catch (IOException e1) {
                    // TODO Auto-generated catch block
                    e1.printStackTrace();
                } catch (InterruptedException e1) {
                    // TODO Auto-generated catch block
                    e1.printStackTrace();
                }}
                else if (e.getSource()==openO){gvLdr.openOther();}
                else if (e.getSource()==backTothy){gvLdr.backload();}
                else if (e.getSource()==reloadI){gvLdr.reloadFile();}
                else if (e.getSource()==globvI){grMngr.getGlobalView();}
                else if (e.getSource()==radarI){grMngr.showRadarView(true);}
                else if (e.getSource()==showBkI){cfgMngr.showBookmarks();}
                else if (e.getSource()==searchI){showSearchBox();}
                
                else if (e.getSource()==unusedI){showUnusedCheck();}
                else if (e.getSource()==tagI){

                    try {
                        TheoremParser.tag_check(FileReader.loadCurrentTheory());
                    } catch (IOException | InterruptedException e1) {
                        // TODO Auto-generated catch block
                        e1.printStackTrace();
                    }
                }
                else if (e.getSource()==backI){grMngr.moveBack();}
                // else if (e.getSource()==fontI){grMngr.assignFontToGraph();}
                else if (e.getSource()==pngI){savePNG();}
                else if (e.getSource()==svgI){saveSVG();}
                else if (e.getSource()==printI){print();}
                // else if (e.getSource()==prefsI){showPreferences();}
                else if (e.getSource()==exitI){exit();}
                // else if (e.getSource()==helpI){help();}
                // else if (e.getSource()==versionI){checkVersion();}
                // else if (e.getSource()==pluginsI){aboutPlugins();}
                // else if (e.getSource()==aboutI){about();}
            }
        };
        JMenuBar jmb=new JMenuBar();
        JMenu jm1=new JMenu("File");
        JMenu jm2=new JMenu("View");
        // JMenu jm3=new JMenu("Help");
        jmb.add(jm1);
        jmb.add(jm2);
        // jmb.add(jm3);
        open.add(openO);
        open.add(openDG);
        open.add(openNG);
        open.add(openCG);
        open.add(openTG);
        open.addSeparator();
        open.add(openO);
        open.addSeparator();
        open.add(openS);
        open.add(openDir);
        open.add(openDirMulti);
        jm1.add(open);
        jm1.add(backTothy);
        jm1.add(reloadI);
        jm1.addSeparator();
        jm1.add(pngI);
        jm1.add(svgI);
        jm1.addSeparator();
        jm1.add(printI);
        jm1.addSeparator();
        jm1.add(exitI);
        jm2.add(backI);
        jm2.add(globvI);
        jm2.add(radarI);
        jm2.addSeparator();
        jm2.add(showBkI);
        jm2.addSeparator();
        jm2.add(searchI);
        jm2.addSeparator();
        jm2.add(tagI);
        jm2.add(unusedI);
        
        // jm2.addSeparator();
        // jm2.add(fontI);
        // jm2.addSeparator();
        // jm2.add(prefsI);
        // jm3.add(helpI);
        // jm3.add(versionI);
        // jm3.add(pluginsI);
        // jm3.add(aboutI);
        openDG.addActionListener(a0);
        openNG.addActionListener(a0);
        openCG.addActionListener(a0);
        openTG.addActionListener(a0);
        openS.addActionListener(a0);
        openDir.addActionListener(a0);
        openDirMulti.addActionListener(a0);
        openO.addActionListener(a0);
        reloadI.addActionListener(a0);
        backTothy.addActionListener(a0);
        pngI.addActionListener(a0);
        svgI.addActionListener(a0);
        printI.addActionListener(a0);
        exitI.addActionListener(a0);
        globvI.addActionListener(a0);
        radarI.addActionListener(a0);
        showBkI.addActionListener(a0);
        searchI.addActionListener(a0);
        tagI.addActionListener(a0);
        unusedI.addActionListener(a0);
        
        backI.addActionListener(a0);
        // fontI.addActionListener(a0);
        // prefsI.addActionListener(a0);
        // helpI.addActionListener(a0);
        // versionI.addActionListener(a0);
        // pluginsI.addActionListener(a0);
        // aboutI.addActionListener(a0);
        return jmb;
    }

    void savePNG(){
        final double[] vr = grMngr.mainView.getVisibleRegion(grMngr.mSpace.getCamera(0));
        SwingWorker sw = new SwingWorker(){
            public  Object construct(){
                new PNGExportWindow(vr[2] - vr[0], vr[1]-vr[3], grMngr);
                return null;
            }
        };
        sw.start();
    }

    void saveSVG(){
        final JFileChooser fc=new JFileChooser(ConfigManager.m_LastExportDir!=null ? ConfigManager.m_LastExportDir : ConfigManager.m_PrjDir);
        fc.setDialogTitle("Export SVG");
        int returnVal=fc.showSaveDialog(grMngr.mainView.getFrame());
        if (returnVal==JFileChooser.APPROVE_OPTION) {
            final SwingWorker worker=new SwingWorker(){
                public Object construct(){
                    exportSVG(fc.getSelectedFile());
                    return null;
                }
            };
            worker.start();
        }
    }

    /*export the entire RDF graph as SVG locally*/
    public void exportSVG(File f){
        if (f!=null){
            grMngr.mainView.setCursorIcon(java.awt.Cursor.WAIT_CURSOR);
            ConfigManager.m_LastExportDir=f.getParentFile();
            setStatusBarText("Exporting to SVG "+f.toString()+" ...");
            if (f.exists()){f.delete();}
            fr.inria.zvtm.svg.SVGWriter svgw=new fr.inria.zvtm.svg.SVGWriter();
            Document d = svgw.exportVirtualSpace(grMngr.mSpace, new DOMImplementationImpl(), f);
            Utils.serialize(d,f);
            setStatusBarText("Exporting to SVG "+f.toString()+" ...done");
            grMngr.mainView.setCursorIcon(java.awt.Cursor.CUSTOM_CURSOR);
        }
    }

    public void setStatusBarText(String s){
        grMngr.mainView.setStatusBarText(s);
    }

    void print(){
        final double[] vr = grMngr.mainView.getVisibleRegion(grMngr.mSpace.getCamera(0));
        SwingWorker sw = new SwingWorker(){
            public  Object construct(){
                new PrintWindow(vr[2] - vr[0], vr[1]-vr[3], grMngr);
                return null;
            }
        };
        sw.start();
    }

    public void displayMainPieMenu(boolean b){
        if (b){
            PieMenuFactory.setItemFillColor(ConfigManager.PIEMENU_FILL_COLOR);
            PieMenuFactory.setItemBorderColor(ConfigManager.PIEMENU_BORDER_COLOR);
            PieMenuFactory.setSelectedItemFillColor(ConfigManager.PIEMENU_INSIDE_COLOR);
            PieMenuFactory.setSelectedItemBorderColor(null);
            PieMenuFactory.setLabelColor(ConfigManager.PIEMENU_BORDER_COLOR);
            PieMenuFactory.setFont(ConfigManager.PIEMENU_FONT);
            if (Utils.osIsWindows() || Utils.osIsMacOS()){PieMenuFactory.setTranslucency(ConfigManager.PIEMENU_MAIN_ALPHA);}
            PieMenuFactory.setSensitivityRadius(0.5);
            PieMenuFactory.setAngle(-Math.PI/2.0);
            PieMenuFactory.setRadius(100);
            mainPieMenu = PieMenuFactory.createPieMenu(Messages.mainMenuLabels, Messages.mainMenuLabelOffsets, 0, grMngr.mainView, grMngr.vsm);
            Glyph[] items = mainPieMenu.getItems();
            items[0].setType(Messages.PM_ENTRY);
            items[1].setType(Messages.PM_SUBMN);
            items[2].setType(Messages.PM_ENTRY);
            items[3].setType(Messages.PM_SUBMN);
        }
        else {
            mainPieMenu.destroy(0);
            mainPieMenu = null;
        }
    }

    public void displaySubMenu(Glyph menuItem, boolean b){
        if (b){
            int index = mainPieMenu.getItemIndex(menuItem);
            if (index != -1){
                String label = mainPieMenu.getLabels()[index].getText();
                PieMenuFactory.setFont(ConfigManager.PIEMENU_FONT);
                PieMenuFactory.setItemFillColor(ConfigManager.PIEMENU_FILL_COLOR);
                PieMenuFactory.setItemBorderColor(ConfigManager.PIEMENU_BORDER_COLOR);
                PieMenuFactory.setSelectedItemFillColor(ConfigManager.PIEMENU_INSIDE_COLOR);
                PieMenuFactory.setSelectedItemBorderColor(null);
                PieMenuFactory.setSensitivityRadius(1.0);
                if (Utils.osIsWindows() || Utils.osIsMacOS()){PieMenuFactory.setTranslucency(ConfigManager.PIEMENU_SUB_ALPHA);}
                PieMenuFactory.setRadius(100);
                Glyph[] items;
                if (label == Messages.PM_FILE){
                    subPieMenu = PieMenuFactory.createPieMenu(Messages.fileMenuLabels, Messages.fileMenuLabelOffsets, 0 , grMngr.mainView, grMngr.vsm);
                    items = subPieMenu.getItems();
                    for (int i=0;i<items.length;i++){
                        items[i].setType(Messages.PM_ENTRY);
                    }
                }
                else if (label == Messages.PM_EXPORT){
                    subPieMenu = PieMenuFactory.createPieMenu(Messages.exportMenuLabels, Messages.exportMenuLabelOffsets, 0 , grMngr.mainView, grMngr.vsm);
                    items = subPieMenu.getItems();
                    for (int i=0;i<items.length;i++){
                        items[i].setType(Messages.PM_ENTRY);
                    }
                }
            }
        }
        else {
            subPieMenu.destroy(0);
            subPieMenu = null;
        }
    }

    public void pieMenuEvent(Glyph menuItem) throws IOException, InterruptedException{
        int index = mainPieMenu.getItemIndex(menuItem);
        String label;
        if (index != -1){
            label = mainPieMenu.getLabels()[index].getText();
            if (label == Messages.PM_BACK){grMngr.moveBack();}
            else if (label == Messages.PM_GLOBALVIEW){grMngr.getGlobalView();}
        }
        else {
            index = subPieMenu.getItemIndex(menuItem);
            if (index != -1){
                label = subPieMenu.getLabels()[index].getText();
                if (label == Messages.PM_OPENDOTSVG){gvLdr.open(DOTManager.DOT_PROGRAM, false);}
                else if (label == Messages.PM_OPENNEATOSVG){gvLdr.open(DOTManager.NEATO_PROGRAM, false);}
                else if (label == Messages.PM_OPENCIRCOSVG){gvLdr.open(DOTManager.CIRCO_PROGRAM, false);}
                else if (label == Messages.PM_OPENTWOPISVG){gvLdr.open(DOTManager.TWOPI_PROGRAM, false);}
                else if (label == Messages.PM_OPENSVG){gvLdr.openSVGFile();}
                else if (label == Messages.PM_OPENDIR){gvLdr.DirLoadSvg();}
                else if (label == Messages.PM_OPENDIRMULTI){gvLdr.DirLoadSvg_multi();}
                else if (label == Messages.PM_OPENOTHER){gvLdr.openOther();}
                else if (label == Messages.PM_EXPSVG){saveSVG();}
                else if (label == Messages.PM_EXPPNG){savePNG();}
                else if (label == Messages.PM_EXPPRINT){print();}
            }
        }
    }

    public PieMenu getMainPieMenu(){
        return mainPieMenu;
    }

    public PieMenu getSubPieMenu(){
        return subPieMenu;
    }

    /* Web & URL */

    //open up the default or user-specified browser (netscape, ie,...) and try to display the content uri
    void displayURLinBrowser(String uri){
    if (ConfigManager.webBrowser==null){ConfigManager.webBrowser=new WebBrowser();}
    ConfigManager.webBrowser.show(uri, grMngr);
    }

    void showPreferences(){
    PrefWindow dp=new PrefWindow(this, grMngr);
    dp.setLocationRelativeTo(grMngr.mainView.getFrame());
    dp.setVisible(true);
    }

    void showSearchBox(){
    SearchBox sb = new SearchBox(grMngr);
    sb.setLocationRelativeTo(grMngr.mainView.getFrame());
    sb.setVisible(true);
    }

    //Unused check
    void showUnusedCheck(){
        UnusedSearch sb = new UnusedSearch();
        sb.setLocationRelativeTo(grMngr.mainView.getFrame());
        sb.setVisible(true);
        }
    


    /** Get the last file opened with ZGRViewer. */
    public File getLastFileOpened(){
        return cfgMngr.lastFileOpened;
    }

    void saveConfiguration(){
    cfgMngr.saveConfig();
    }

    void help(){
    TextViewer tv=new TextViewer(new StringBuffer(Messages.commands),"Commands",0,false);
    tv.setLocationRelativeTo(grMngr.mainView.getFrame());
    tv.setVisible(true);
    }

    public void about(){
    JOptionPane.showMessageDialog(grMngr.mainView.getFrame(),Messages.about);
    }

    public void aboutPlugins(){
        cfgMngr.showPluginInfo();
    }

    static final String CURRENT_VERSION_URL = "http://zvtm.sourceforge.net/zgrviewer/currentVersion";


    public void checkVersion(){
        try {
            String version = Utils.getTextContent(new URL(CURRENT_VERSION_URL), 10).trim();
            if (version != null){
                if (version.equals(Messages.VERSION)){
                    // we should actually compare numbers
                    JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), Messages.YOU_HAVE_THE_MOST_RECENT_VERSION,
                        "Version Information", JOptionPane.INFORMATION_MESSAGE);
                }
                else {
                    JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), Messages.NEW_VERSION_AVAILABLE+version+"\n"+Messages.DOWNLOAD_URL,
                        "Version Information", JOptionPane.INFORMATION_MESSAGE);
                }
            }
            else {
                JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), Messages.COULD_NOT_GET_VERSION_INFO, "Error", JOptionPane.ERROR_MESSAGE);
            }
        }
        catch (Exception ex){
            JOptionPane.showMessageDialog(grMngr.mainView.getFrame(), Messages.COULD_NOT_GET_VERSION_INFO, "Error", JOptionPane.ERROR_MESSAGE);
        }
    }

    public void exit(){
        // cfgMngr.saveCommandLines();
        // grMngr.paMngr.stop();
        // cfgMngr.terminatePlugins();
        // if (exitVMonClose()){
            System.exit(0);
        // }
    }

    // public static void main(String[] args){
    //     ZGROptions options = new ZGROptions();
    //     CmdLineParser parser = new CmdLineParser(options);
    //     try {
    //         parser.parseArgument(args);
    //     } catch(CmdLineException ex){
    //         System.err.println(ex.getMessage());
    //         parser.printUsage(System.err);
    //         return;
    //     }
    //     if (!options.fullscreen && Utils.osIsMacOS()){
    //         System.setProperty("apple.laf.useScreenMenuBar", "true");
    //     }
    //     System.out.println("--help for command line options");
    //     new ZGRViewer(options);
    // }

}
