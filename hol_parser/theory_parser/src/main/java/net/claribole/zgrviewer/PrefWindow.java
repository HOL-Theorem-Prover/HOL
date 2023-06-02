/*   FILE: PrefWindow.java
 *   DATE OF CREATION:   Thu Jan 09 15:47:07 2003
 *   Copyright (c) Emmanuel Pietriga, 2002. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2010. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *   $Id: PrefWindow.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.io.File;

import javax.swing.BorderFactory;
import javax.swing.ButtonGroup;
import javax.swing.JScrollPane;
import javax.swing.JComponent;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JSlider;
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import javax.swing.JColorChooser;
import javax.swing.JSpinner;
import javax.swing.SpinnerNumberModel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import fr.inria.zvtm.glyphs.Glyph;

class PrefWindow extends JFrame implements ActionListener, MouseListener {

    ZGRViewer application;
    GraphicsManager grMngr;

    JTabbedPane tabbedPane;

    JButton okPrefs,savePrefs;

    //Misc prefs
    JCheckBox saveWindowLayoutCb, dynaspotCb;
    JCheckBox antialiascb, silentCb;
    JTextField cmdLOptsTf;
    JCheckBox sdZoomCb;
    JSlider sdZoomSlider;
    JSpinner mFactorSpinner;
    ColorIndicator highlightColor;

    //directory panel
    JButton browseTmpDirBt,browseGraphDirBt,browseNeatoBt,browseCircoBt,browseTwopiBt,browseDotBt,browseFontDirBt;
    JTextField tmpDirTF,graphDirTF,neatoPathTF,circoPathTF,twopiPathTF,dotPathTF,fontDirTF;
    JCheckBox cb1;

    //web browser panel
    JRadioButton detectBrowserBt,specifyBrowserBt;
    JTextField browserPathTf,browserOptsTf;
    JButton brw6,webHelpBt;
    JLabel pathLb,optLb;

    //proxy/firewall
    JCheckBox useProxyCb;
    JLabel proxyHostLb,proxyPortLb;
    JTextField proxyHostTf,proxyPortTf;
    JButton proxyHelpBt;

    PrefWindow(ZGRViewer app, GraphicsManager gm){
    this.application=app;
    this.grMngr = gm;
    tabbedPane = new JTabbedPane();

    //misc panel
    JPanel miscPane=new JPanel();
    GridBagLayout gridBag0=new GridBagLayout();
    GridBagConstraints constraints0=new GridBagConstraints();
    constraints0.fill=GridBagConstraints.HORIZONTAL;
    constraints0.anchor=GridBagConstraints.WEST;
    miscPane.setLayout(gridBag0);

    //save window layout checkbox
    saveWindowLayoutCb=new JCheckBox("Save/Restore Window Layout at Startup",ConfigManager.SAVE_WINDOW_LAYOUT);
    Utils.buildConstraints(constraints0,0,0,2,1,100,10);
    gridBag0.setConstraints(saveWindowLayoutCb,constraints0);
    miscPane.add(saveWindowLayoutCb);
    // activate dynaspot pointing
    dynaspotCb = new JCheckBox("Activate DynaSpot pointing", ConfigManager.DYNASPOT);
    dynaspotCb.addActionListener(this);
    Utils.buildConstraints(constraints0,0,1,2,1,100,10);
    gridBag0.setConstraints(dynaspotCb,constraints0);
    miscPane.add(dynaspotCb);
    //antialiasing
    antialiascb=new JCheckBox("Antialiasing",ConfigManager.ANTIALIASING);
    antialiascb.addActionListener(this);
    Utils.buildConstraints(constraints0,0,2,2,1,100,10);
    gridBag0.setConstraints(antialiascb,constraints0);
    miscPane.add(antialiascb);
    // -q option
    silentCb = new JCheckBox("GraphViz programs should not issue warnings (v1.10 and above)", ConfigManager.FORCE_SILENT);
    silentCb.addActionListener(this);
    Utils.buildConstraints(constraints0, 0, 3, 2, 1, 100, 10);
    gridBag0.setConstraints(silentCb,constraints0);
    miscPane.add(silentCb);
    //command line options
    JLabel cmdLOptsLb=new JLabel("dot/neato command line options (-T will be ignored)");
    Utils.buildConstraints(constraints0,0,4,2,1,100,10);
    gridBag0.setConstraints(cmdLOptsLb,constraints0);
    miscPane.add(cmdLOptsLb);
    cmdLOptsTf=new JTextField(ConfigManager.CMD_LINE_OPTS);
    Utils.buildConstraints(constraints0,0,5,2,1,100,10);
    gridBag0.setConstraints(cmdLOptsTf,constraints0);
    miscPane.add(cmdLOptsTf);
    sdZoomCb = new JCheckBox("Enable speed-dependent automatic zooming");
    Utils.buildConstraints(constraints0,0,6,2,1,100,10);
    gridBag0.setConstraints(sdZoomCb,constraints0);
    miscPane.add(sdZoomCb);
    sdZoomCb.setSelected(application.cfgMngr.isSDZoomEnabled());
    ActionListener a31 = new ActionListener(){
        public void actionPerformed(ActionEvent e){
            boolean b = PrefWindow.this.sdZoomCb.isSelected();
            PrefWindow.this.application.cfgMngr.setSDZoomEnabled(b);
            PrefWindow.this.sdZoomSlider.setEnabled(b);
        }
        };
    sdZoomCb.addActionListener(a31);
    sdZoomSlider = new JSlider(2, 10, (int)application.cfgMngr.getSDZoomFactor());
    sdZoomSlider.setLabelTable(sdZoomSlider.createStandardLabels(1));
    sdZoomSlider.setPaintLabels(true);
    sdZoomSlider.setPaintTicks(true);
    sdZoomSlider.setSnapToTicks(true);
    sdZoomSlider.setPaintTrack(true);
    sdZoomSlider.setEnabled(application.cfgMngr.isSDZoomEnabled());
    Utils.buildConstraints(constraints0,0,7,2,1,100,10);
    gridBag0.setConstraints(sdZoomSlider,constraints0);
    miscPane.add(sdZoomSlider);
    ChangeListener cl0 = new ChangeListener(){
        public void stateChanged(ChangeEvent e){
            PrefWindow.this.application.cfgMngr.setSDZoomFactor((double)PrefWindow.this.sdZoomSlider.getValue());
        }
        };
    sdZoomSlider.addChangeListener(cl0);
    JLabel mFactorLabel = new JLabel("Magnification factor when focusing on a node");
    Utils.buildConstraints(constraints0, 0, 8, 1, 1, 60, 10);
    gridBag0.setConstraints(mFactorLabel, constraints0);
    miscPane.add(mFactorLabel);
    mFactorSpinner = new JSpinner(new SpinnerNumberModel((float)ConfigManager.MAG_FACTOR, 0.1, 10, 0.1));
    Utils.buildConstraints(constraints0, 1, 8, 1, 1, 40, 0);
    gridBag0.setConstraints(mFactorSpinner, constraints0);
    miscPane.add(mFactorSpinner);


    JLabel highlightLb = new JLabel("Color of highlighted elements");
    Utils.buildConstraints(constraints0, 0, 9, 1, 1, 60, 10);
    gridBag0.setConstraints(highlightLb, constraints0);
    miscPane.add(highlightLb);
    highlightColor = new ColorIndicator(ConfigManager.HIGHLIGHT_COLOR);
    Utils.buildConstraints(constraints0, 1, 9, 1, 1, 40, 0);
    gridBag0.setConstraints(highlightColor, constraints0);
    miscPane.add(highlightColor);
    highlightColor.addMouseListener(this);

    //blank panel to fill remaining part of the tab
    JPanel p1=new JPanel();
    Utils.buildConstraints(constraints0,0,10,1,1,100,50);
    gridBag0.setConstraints(p1,constraints0);
    miscPane.add(p1);
    //add tab to panel
    tabbedPane.addTab("Misc.",miscPane);

    //directories panel
    FocusListener fl0=new FocusListener(){
        public void focusGained(FocusEvent e){}
        public void focusLost(FocusEvent e){
            Object src = e.getSource();
            if (src == tmpDirTF){
            File fl = new File(tmpDirTF.getText().trim());
            if (fl.exists()){
                if (fl.isDirectory()){
                ConfigManager.m_TmpDir = fl;
                }
                else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.notADirectory + tmpDirTF.getText());
                }
            }
            else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.fileDoesNotExist + tmpDirTF.getText());
            }
            }
            else if (src == graphDirTF){
            File fl = new File(graphDirTF.getText().trim());
            if (fl.exists()){
                if (fl.isDirectory()){
                ConfigManager.m_PrjDir = fl;
                }
                else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.notADirectory + graphDirTF.getText());
                }
            }
            else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.fileDoesNotExist + graphDirTF.getText());
            }
            }
            else if (src == neatoPathTF){
            File fl = new File(neatoPathTF.getText().trim());
            if (fl.exists()){
                if (fl.isFile()){
                ConfigManager.m_NeatoPath = fl;
                }
                else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.notADirectory + neatoPathTF.getText());
                }
            }
            else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.fileDoesNotExist + neatoPathTF.getText());
            }
            }
            else if (src == circoPathTF){
            File fl = new File(circoPathTF.getText().trim());
            if (fl.exists()){
                if (fl.isFile()){
                ConfigManager.m_CircoPath = fl;
                }
                else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this, Messages.notADirectory + circoPathTF.getText());
                }
            }
            else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this, Messages.fileDoesNotExist + circoPathTF.getText());
            }
            }
            else if (src == twopiPathTF){
            File fl = new File(twopiPathTF.getText().trim());
            if (fl.exists()){
                if (fl.isFile()){
                ConfigManager.m_TwopiPath = fl;
                }
                else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this, Messages.notADirectory + twopiPathTF.getText());
                }
            }
            else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this, Messages.fileDoesNotExist + twopiPathTF.getText());
            }
            }
            else if (src == dotPathTF){
            File fl = new File(dotPathTF.getText().trim());
            if (fl.exists()){
                if (fl.isFile()){
                ConfigManager.m_DotPath = fl;
                }
                else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.notAFile + dotPathTF.getText());
                }
            }
            else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.fileDoesNotExist + dotPathTF.getText());
            }
            }
            else if (src == fontDirTF){
            File fl = new File(fontDirTF.getText().trim());
            if (fl.exists()){
                if (fl.isDirectory()){
                ConfigManager.m_GraphVizFontDir = fl;
                }
                else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.notADirectory + fontDirTF.getText());
                }
            }
            else {
                javax.swing.JOptionPane.showMessageDialog(PrefWindow.this,Messages.fileDoesNotExist + fontDirTF.getText());
            }
            }
        }
        };
    JPanel dirPane=new JPanel();
    GridBagLayout gridBag=new GridBagLayout();
    GridBagConstraints constraints=new GridBagConstraints();
    constraints.fill=GridBagConstraints.HORIZONTAL;
    constraints.anchor=GridBagConstraints.WEST;
    dirPane.setLayout(gridBag);
    JLabel l1=new JLabel("Temporary directory");
    Utils.buildConstraints(constraints,0,0,1,1,60,10);
    gridBag.setConstraints(l1,constraints);
    dirPane.add(l1);
    cb1=new JCheckBox("Delete temp files on exit");
    Utils.buildConstraints(constraints,1,0,1,1,30,0);
    gridBag.setConstraints(cb1,constraints);
    if (ConfigManager.DELETE_TEMP_FILES){cb1.setSelected(true);} else {cb1.setSelected(false);}
    cb1.addActionListener(this);
    dirPane.add(cb1);
    browseTmpDirBt=new JButton("Browse...");
    Utils.buildConstraints(constraints,2,0,1,1,10,0);
    gridBag.setConstraints(browseTmpDirBt,constraints);
    browseTmpDirBt.addActionListener(this);
    dirPane.add(browseTmpDirBt);
    tmpDirTF=new JTextField(ConfigManager.m_TmpDir.toString());
    Utils.buildConstraints(constraints,0,1,3,1,100,10);
    gridBag.setConstraints(tmpDirTF,constraints);
    dirPane.add(tmpDirTF);
    tmpDirTF.addFocusListener(fl0);
    JLabel l2=new JLabel("DOT files directory");
    Utils.buildConstraints(constraints,0,2,2,1,90,10);
    gridBag.setConstraints(l2,constraints);
    dirPane.add(l2);
    browseGraphDirBt=new JButton("Browse...");
    Utils.buildConstraints(constraints,2,2,1,1,10,0);
    gridBag.setConstraints(browseGraphDirBt,constraints);
    browseGraphDirBt.addActionListener(this);
    dirPane.add(browseGraphDirBt);
    graphDirTF=new JTextField(ConfigManager.m_PrjDir.toString());
    Utils.buildConstraints(constraints,0,3,3,1,100,10);
    gridBag.setConstraints(graphDirTF,constraints);
    dirPane.add(graphDirTF);
    graphDirTF.addFocusListener(fl0);
    JLabel l4=new JLabel("GraphViz/dot executable");
    Utils.buildConstraints(constraints,0,4,2,1,90,10);
    gridBag.setConstraints(l4,constraints);
    dirPane.add(l4);
    browseDotBt=new JButton("Browse...");
    Utils.buildConstraints(constraints,2,4,1,1,10,0);
    gridBag.setConstraints(browseDotBt,constraints);
    browseDotBt.addActionListener(this);
    dirPane.add(browseDotBt);
    dotPathTF=new JTextField(ConfigManager.m_DotPath.toString());
    Utils.buildConstraints(constraints,0,5,3,1,100,10);
    gridBag.setConstraints(dotPathTF,constraints);
    dirPane.add(dotPathTF);
    dotPathTF.addFocusListener(fl0);
    JLabel l3=new JLabel("GraphViz/neato executable");
    Utils.buildConstraints(constraints,0,6,2,1,90,10);
    gridBag.setConstraints(l3,constraints);
    dirPane.add(l3);
    browseNeatoBt=new JButton("Browse...");
    Utils.buildConstraints(constraints,2,6,1,1,10,0);
    gridBag.setConstraints(browseNeatoBt,constraints);
    browseNeatoBt.addActionListener(this);
    dirPane.add(browseNeatoBt);
    neatoPathTF=new JTextField(ConfigManager.m_NeatoPath.toString());
    Utils.buildConstraints(constraints,0,7,3,1,100,10);
    gridBag.setConstraints(neatoPathTF,constraints);
    dirPane.add(neatoPathTF);
    neatoPathTF.addFocusListener(fl0);
    JLabel l3b=new JLabel("GraphViz/circo executable");
    Utils.buildConstraints(constraints,0,8,2,1,90,10);
    gridBag.setConstraints(l3b,constraints);
    dirPane.add(l3b);
    browseCircoBt=new JButton("Browse...");
    Utils.buildConstraints(constraints,2,8,1,1,10,0);
    gridBag.setConstraints(browseCircoBt,constraints);
    browseCircoBt.addActionListener(this);
    dirPane.add(browseCircoBt);
    circoPathTF=new JTextField(ConfigManager.m_CircoPath.toString());
    Utils.buildConstraints(constraints,0,9,3,1,100,10);
    gridBag.setConstraints(circoPathTF,constraints);
    dirPane.add(circoPathTF);
    circoPathTF.addFocusListener(fl0);
    JLabel l3c=new JLabel("GraphViz/twopi executable");
    Utils.buildConstraints(constraints,0,10,2,1,90,10);
    gridBag.setConstraints(l3c,constraints);
    dirPane.add(l3c);
    browseTwopiBt=new JButton("Browse...");
    Utils.buildConstraints(constraints,2,10,1,1,10,0);
    gridBag.setConstraints(browseTwopiBt,constraints);
    browseTwopiBt.addActionListener(this);
    dirPane.add(browseTwopiBt);
    twopiPathTF=new JTextField(ConfigManager.m_TwopiPath.toString());
    Utils.buildConstraints(constraints,0,11,3,1,100,10);
    gridBag.setConstraints(twopiPathTF,constraints);
    dirPane.add(twopiPathTF);
    twopiPathTF.addFocusListener(fl0);
    JLabel l5=new JLabel("GraphViz font directory (optional)");
    Utils.buildConstraints(constraints,0,12,2,1,90,10);
    gridBag.setConstraints(l5,constraints);
    dirPane.add(l5);
    browseFontDirBt=new JButton("Browse...");
    Utils.buildConstraints(constraints,2,12,1,1,10,0);
    gridBag.setConstraints(browseFontDirBt,constraints);
    browseFontDirBt.addActionListener(this);
    dirPane.add(browseFontDirBt);
    fontDirTF=new JTextField(ConfigManager.m_GraphVizFontDir.toString());
    Utils.buildConstraints(constraints,0,13,3,1,100,10);
    gridBag.setConstraints(fontDirTF,constraints);
    dirPane.add(fontDirTF);
    fontDirTF.addFocusListener(fl0);
    JScrollPane dirSP = new JScrollPane(dirPane);
    dirSP.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED);
    dirSP.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
    tabbedPane.addTab("Directories", dirSP);
    //web browser panel
    JPanel webPane=new JPanel();
    GridBagLayout gridBag2=new GridBagLayout();
    GridBagConstraints constraints2=new GridBagConstraints();
    constraints2.fill=GridBagConstraints.HORIZONTAL;
    constraints2.anchor=GridBagConstraints.WEST;
    webPane.setLayout(gridBag2);
    ButtonGroup bg2=new ButtonGroup();
    detectBrowserBt=new JRadioButton("Automatically Detect Default Browser");
    Utils.buildConstraints(constraints2,0,0,3,1,100,1);
    gridBag2.setConstraints(detectBrowserBt,constraints2);
    detectBrowserBt.addActionListener(this);
    bg2.add(detectBrowserBt);
    webPane.add(detectBrowserBt);
    specifyBrowserBt=new JRadioButton("Specify Browser:");
    Utils.buildConstraints(constraints2,0,1,3,1,100,1);
    gridBag2.setConstraints(specifyBrowserBt,constraints2);
    specifyBrowserBt.addActionListener(this);
    bg2.add(specifyBrowserBt);
    webPane.add(specifyBrowserBt);
    JPanel p7=new JPanel();
    Utils.buildConstraints(constraints2,0,2,1,1,10,1);
    gridBag2.setConstraints(p7,constraints2);
    webPane.add(p7);
    pathLb=new JLabel("Path");
    Utils.buildConstraints(constraints2,1,2,1,1,80,0);
    gridBag2.setConstraints(pathLb,constraints2);
    webPane.add(pathLb);
    brw6=new JButton("Browse...");
    Utils.buildConstraints(constraints2,2,2,1,1,10,0);
    gridBag2.setConstraints(brw6,constraints2);
    brw6.addActionListener(this);
    webPane.add(brw6);
    browserPathTf=new JTextField(ConfigManager.browserPath.toString());
    Utils.buildConstraints(constraints2,1,3,2,1,90,1);
    gridBag2.setConstraints(browserPathTf,constraints2);
    webPane.add(browserPathTf);
    optLb=new JLabel("Command Line Options");
    Utils.buildConstraints(constraints2,1,4,2,1,90,1);
    gridBag2.setConstraints(optLb,constraints2);
    webPane.add(optLb);
    browserOptsTf=new JTextField(ConfigManager.browserOptions);
    Utils.buildConstraints(constraints2,1,5,2,1,90,1);
    gridBag2.setConstraints(browserOptsTf,constraints2);
    webPane.add(browserOptsTf);
    //fill out empty space
    JPanel p8=new JPanel();
    Utils.buildConstraints(constraints2,0,6,3,1,100,92);
    gridBag2.setConstraints(p8,constraints2);
    webPane.add(p8);
    webHelpBt=new JButton("Help");
    Utils.buildConstraints(constraints2,2,7,1,1,10,1);
    gridBag2.setConstraints(webHelpBt,constraints2);
    webHelpBt.addActionListener(this);
    webPane.add(webHelpBt);
    if (ConfigManager.autoDetectBrowser){detectBrowserBt.doClick();} //select and fire event
    else {specifyBrowserBt.doClick();} //so that fields get enabled/disabled as is approriate
    tabbedPane.addTab("Web Browser",webPane);

    //proxy panel
    JPanel proxyPane=new JPanel();
    GridBagLayout gridBag5=new GridBagLayout();
    GridBagConstraints constraints5=new GridBagConstraints();
    constraints5.fill=GridBagConstraints.HORIZONTAL;
    constraints5.anchor=GridBagConstraints.WEST;
    proxyPane.setLayout(gridBag5);
    useProxyCb=new JCheckBox("Use Proxy Server");
    Utils.buildConstraints(constraints5,0,0,2,1,100,1);
    gridBag5.setConstraints(useProxyCb,constraints5);
    useProxyCb.setSelected(ConfigManager.useProxy);
    useProxyCb.addActionListener(this);
    proxyPane.add(useProxyCb);
    proxyHostLb=new JLabel("Hostname:");
    proxyHostLb.setEnabled(ConfigManager.useProxy);
    Utils.buildConstraints(constraints5,0,1,1,1,80,1);
    gridBag5.setConstraints(proxyHostLb,constraints5);
    proxyPane.add(proxyHostLb);
    proxyPortLb=new JLabel("Port:");
    proxyPortLb.setEnabled(ConfigManager.useProxy);
    Utils.buildConstraints(constraints5,1,1,1,1,20,1);
    gridBag5.setConstraints(proxyPortLb,constraints5);
    proxyPane.add(proxyPortLb);
    proxyHostTf=new JTextField(ConfigManager.proxyHost);
    proxyHostTf.setEnabled(ConfigManager.useProxy);
    Utils.buildConstraints(constraints5,0,2,1,1,80,1);
    gridBag5.setConstraints(proxyHostTf,constraints5);
    proxyPane.add(proxyHostTf);
    proxyPortTf=new JTextField(ConfigManager.proxyPort);
    proxyPortTf.setEnabled(ConfigManager.useProxy);
    Utils.buildConstraints(constraints5,1,2,1,1,20,1);
    gridBag5.setConstraints(proxyPortTf,constraints5);
    proxyPane.add(proxyPortTf);
    constraints5.fill=GridBagConstraints.BOTH;
    constraints5.anchor=GridBagConstraints.CENTER;
    //fill out empty space
    JPanel p1000=new JPanel();
    Utils.buildConstraints(constraints5,0,5,2,1,100,90);
    gridBag5.setConstraints(p1000,constraints5);
    proxyPane.add(p1000);
    constraints5.fill=GridBagConstraints.NONE;
    constraints5.anchor=GridBagConstraints.EAST;
    proxyHelpBt=new JButton("Help");
    Utils.buildConstraints(constraints5,1,6,1,1,20,1);
    gridBag5.setConstraints(proxyHelpBt,constraints5);
    proxyHelpBt.addActionListener(this);
    proxyPane.add(proxyHelpBt);
    tabbedPane.addTab("Proxy",proxyPane);

    //plugin panel
    tabbedPane.addTab("Plugins", initPluginPane());

    //main panel (tabbed panes + OK/Save buttons)
    Container cpane=this.getContentPane();
    GridBagLayout gridBag3=new GridBagLayout();
    GridBagConstraints constraints3=new GridBagConstraints();
    constraints3.fill=GridBagConstraints.BOTH;
    constraints3.anchor=GridBagConstraints.WEST;
    cpane.setLayout(gridBag3);
    Utils.buildConstraints(constraints3,0,0,3,1,100,90);
    gridBag3.setConstraints(tabbedPane,constraints3);
    cpane.add(tabbedPane);
    JPanel tmp=new JPanel();
    Utils.buildConstraints(constraints3,0,1,1,1,70,10);
    gridBag3.setConstraints(tmp,constraints3);
    cpane.add(tmp);
    constraints3.fill=GridBagConstraints.HORIZONTAL;
    constraints3.anchor=GridBagConstraints.CENTER;
    okPrefs=new JButton("Apply & Close");
    //okPrefs.setPreferredSize(new Dimension(60,25));
    Utils.buildConstraints(constraints3,1,1,1,1,15,10);
    gridBag3.setConstraints(okPrefs,constraints3);
    okPrefs.addActionListener(this);
    cpane.add(okPrefs);
    constraints3.fill=GridBagConstraints.HORIZONTAL;
    constraints3.anchor=GridBagConstraints.CENTER;
    savePrefs=new JButton("Save");
    //savePrefs.setPreferredSize(new Dimension(60,35));
    Utils.buildConstraints(constraints3,2,1,1,1,15,10);
    gridBag3.setConstraints(savePrefs,constraints3);
    savePrefs.addActionListener(this);
    cpane.add(savePrefs);

    tabbedPane.setSelectedIndex(0);
    //window
    WindowListener w0=new WindowAdapter(){
        public void windowClosing(WindowEvent e){}
        };
    this.addWindowListener(w0);
    this.setTitle("Preferences");
    this.pack();
    this.setSize(400,360);
    }

    private JComponent initPluginPane(){
    JPanel pluginPane = new JPanel();
    int nbPlugins = application.cfgMngr.plugins.length;

    GridBagLayout gridBag = new GridBagLayout();
    GridBagConstraints constraints = new GridBagConstraints();
    constraints.fill=GridBagConstraints.NONE;
    pluginPane.setLayout(gridBag);
    JButton b65;
    JLabel l65;
    ActionListener a65;
    MouseListener m65;
    int row = 0;
    for (int i=0;i<nbPlugins;i++){
        row = i * 2;
        constraints.anchor = GridBagConstraints.WEST;
        final String url = (application.cfgMngr.plugins[i].getURL() != null) ? application.cfgMngr.plugins[i].getURL().toString() : "";
        l65 = new JLabel("<html><a href=\""+url+"\">"+application.cfgMngr.plugins[i].getName()+"</a></html>");
        Utils.buildConstraints(constraints, 0, row, 1, 1, 70, 5);
        gridBag.setConstraints(l65, constraints);
        pluginPane.add(l65);
        m65 = new MouseListener(){
            public void mouseClicked(MouseEvent e){
            if (url != null && url.length() > 0){
                application.displayURLinBrowser(url);
            }
            }
            public void mouseEntered(MouseEvent e){}
            public void mouseExited(MouseEvent e){}
            public void mousePressed(MouseEvent e){}
            public void mouseReleased(MouseEvent e){}
        };
        l65.addMouseListener(m65);
        constraints.anchor = GridBagConstraints.EAST;
        b65 = new JButton("Settings...");
        Utils.buildConstraints(constraints, 1, row, 1, 1, 30, 0);
        gridBag.setConstraints(b65, constraints);
        pluginPane.add(b65);
        final Plugin pg65 = application.cfgMngr.plugins[i];
        a65 = new ActionListener(){
            public void actionPerformed(ActionEvent e){
            pg65.showSettings();
            }
        };
        b65.addActionListener(a65);
        constraints.anchor = GridBagConstraints.WEST;
        l65 = new JLabel("Author: "+application.cfgMngr.plugins[i].getAuthor());
        Utils.buildConstraints(constraints, 0, row + 1, 1, 1, 0, 5);
        gridBag.setConstraints(l65, constraints);
        pluginPane.add(l65);
        constraints.anchor = GridBagConstraints.EAST;
        l65 = new JLabel("Version: "+application.cfgMngr.plugins[i].getVersion());
        Utils.buildConstraints(constraints, 0, row + 1, 1, 1, 0, 0);
        gridBag.setConstraints(l65, constraints);
        pluginPane.add(l65);
    }
    JPanel p47 = new JPanel();
    constraints.fill=GridBagConstraints.BOTH;
    constraints.anchor = GridBagConstraints.WEST;
    Utils.buildConstraints(constraints, 0, row + 2, 2, 1, 100, 90);
    gridBag.setConstraints(p47, constraints);
    pluginPane.add(p47);
    return new JScrollPane(pluginPane, JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
    }

    public void actionPerformed(ActionEvent e){
        JFileChooser fc;
        int returnVal;
        Object o=e.getSource();
        if (o==browseTmpDirBt){
            //tmp directory browse button
            fc=new JFileChooser(ConfigManager.m_TmpDir);
            fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
            returnVal= fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.m_TmpDir=fc.getSelectedFile();
                tmpDirTF.setText(ConfigManager.m_TmpDir.toString());
            }
        }
        else if (o==browseGraphDirBt){
            fc=new JFileChooser(ConfigManager.m_PrjDir);
            fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
            returnVal= fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.m_PrjDir=fc.getSelectedFile();
                graphDirTF.setText(ConfigManager.m_PrjDir.toString());
            }
        }
        else if (o==browseDotBt){
            fc=new JFileChooser(ConfigManager.m_DotPath);
            fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
            returnVal= fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.m_DotPath=fc.getSelectedFile();
                dotPathTF.setText(ConfigManager.m_DotPath.toString());
            }
        }
        else if (o==browseNeatoBt){
            fc=new JFileChooser(ConfigManager.m_NeatoPath);
            fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
            returnVal= fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.m_NeatoPath=fc.getSelectedFile();
                neatoPathTF.setText(ConfigManager.m_NeatoPath.toString());
            }
        }
        else if (o == browseCircoBt){
            fc = new JFileChooser(ConfigManager.m_CircoPath);
            fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
            returnVal = fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.m_CircoPath = fc.getSelectedFile();
                circoPathTF.setText(ConfigManager.m_CircoPath.toString());
            }
        }
        else if (o==browseTwopiBt){
            fc = new JFileChooser(ConfigManager.m_TwopiPath);
            fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
            returnVal = fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.m_TwopiPath = fc.getSelectedFile();
                twopiPathTF.setText(ConfigManager.m_TwopiPath.toString());
            }
        }
        else if (o==browseFontDirBt){
            fc=new JFileChooser(ConfigManager.m_GraphVizFontDir);
            fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
            returnVal= fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.m_GraphVizFontDir=fc.getSelectedFile();
                fontDirTF.setText(ConfigManager.m_GraphVizFontDir.toString());
            }
        }
        else if (o==cb1){
            if (cb1.isSelected()){ConfigManager.DELETE_TEMP_FILES=true;}
            else {ConfigManager.DELETE_TEMP_FILES=false;}
        }
        else if (o==detectBrowserBt){
            if (detectBrowserBt.isSelected()){
                //automatically detect browser
                ConfigManager.autoDetectBrowser=true;
                browserPathTf.setEnabled(false);
                brw6.setEnabled(false);
                browserOptsTf.setEnabled(false);
                pathLb.setEnabled(false);
                optLb.setEnabled(false);
            }
        }
        else if (o==specifyBrowserBt){
            if (specifyBrowserBt.isSelected()){
                //specify browser
                ConfigManager.autoDetectBrowser=false;
                browserPathTf.setEnabled(true);
                brw6.setEnabled(true);
                browserOptsTf.setEnabled(true);
                pathLb.setEnabled(true);
                optLb.setEnabled(true);
            }
        }
        else if (o==brw6){
            fc=new JFileChooser(ConfigManager.browserPath);
            fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
            returnVal= fc.showOpenDialog(this);
            if (returnVal == JFileChooser.APPROVE_OPTION){
                ConfigManager.browserPath=fc.getSelectedFile();
                browserPathTf.setText(ConfigManager.browserPath.toString());
            }
        }
        else if (o==webHelpBt){
            Dimension screenSize=java.awt.Toolkit.getDefaultToolkit().getScreenSize();
            TextViewer help=new TextViewer(new StringBuffer(Messages.webBrowserHelpText),"Web Browser Configuration",0,(screenSize.width-400)/2,(screenSize.height-300)/2,400,300,false);
        }
        else if (o==useProxyCb){
            proxyHostLb.setEnabled(useProxyCb.isSelected());
            proxyPortLb.setEnabled(useProxyCb.isSelected());
            proxyHostTf.setEnabled(useProxyCb.isSelected());
            proxyPortTf.setEnabled(useProxyCb.isSelected());
        }
        else if (o==proxyHelpBt){
            Dimension screenSize=java.awt.Toolkit.getDefaultToolkit().getScreenSize();
            TextViewer help=new TextViewer(new StringBuffer(Messages.proxyHelpText),"Proxy Configuration",0,(screenSize.width-400)/2,(screenSize.height-300)/2,400,300,false);
        }
        else if (o==okPrefs){updateVars();this.dispose();}
        else if (o==savePrefs){updateVars();application.saveConfiguration();}
        else if (o==antialiascb){
            if (antialiascb.isSelected()){javax.swing.JOptionPane.showMessageDialog(this,Messages.antialiasingWarning);}
            grMngr.setAntialiasing(antialiascb.isSelected());
        }
        else if (o==dynaspotCb){
            grMngr.activateDynaSpot(dynaspotCb.isSelected(), true);
        }
    }

    public void mouseClicked(MouseEvent e){
    Object o = e.getSource();
    if (o == highlightColor){
        Color newCol = JColorChooser.showDialog(this, "Highlight Color", highlightColor.getColor());
        if (newCol != null){
        ConfigManager.HIGHLIGHT_COLOR = newCol;
        highlightColor.setColor(ConfigManager.HIGHLIGHT_COLOR);
        Glyph.setDefaultCursorInsideHighlightColor(ConfigManager.HIGHLIGHT_COLOR);
        }
    }
    }
    public void mousePressed(MouseEvent e){}
    public void mouseReleased(MouseEvent e){}
    public void mouseEntered(MouseEvent e){}
    public void mouseExited(MouseEvent e){}

    void updateVars(){
    ConfigManager.SAVE_WINDOW_LAYOUT=saveWindowLayoutCb.isSelected();
    ConfigManager.FORCE_SILENT = silentCb.isSelected();
    ConfigManager.MAG_FACTOR = ((Double)mFactorSpinner.getValue()).floatValue();
    ConfigManager.CMD_LINE_OPTS=cmdLOptsTf.getText();
    ConfigManager.browserPath=new File(browserPathTf.getText());
    ConfigManager.browserOptions=browserOptsTf.getText();
    ConfigManager.updateProxy(useProxyCb.isSelected(),proxyHostTf.getText(),proxyPortTf.getText());
    }


}

class ColorIndicator extends JPanel {

    Color color;

    ColorIndicator(Color c){
    super();
    color = c;
    setBorder(BorderFactory.createLineBorder(Color.BLACK));
    this.setBackground(color);
    }

    void setColor(Color c){
    color = c;
    this.setBackground(color);
    repaint();
    }

    Color getColor(){
    return color;
    }

}
