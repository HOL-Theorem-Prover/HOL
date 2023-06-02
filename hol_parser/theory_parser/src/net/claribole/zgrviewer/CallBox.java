/*   FILE: CallBox.java
 *   DATE OF CREATION:  Tue Oct 11 13:42:46 2005
 *   Copyright (c) INRIA, 2004-2009. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: CallBox.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Frame;
import java.awt.Container;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;

import javax.swing.JButton;

import javax.swing.JLabel;

import javax.swing.JOptionPane;
import javax.swing.JTextField;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JComboBox;

import java.util.Vector;

import java.io.File;

import fr.inria.zvtm.engine.SwingWorker;

class CallBox extends JDialog implements ActionListener {

    static int FRAME_WIDTH = 400;
    static int FRAME_HEIGHT = 150;

    static String CMD_LINE = "";

    ZGRViewer application;
    GraphicsManager grMngr;

    JComboBox cmdLineCbb;
    JTextField srcFileTf;
    JButton brwBt, openBt, cancelBt;

    CallBox(ZGRViewer app, GraphicsManager gm){
    super((Frame)gm.mainView.getFrame());
    this.application = app;
    this.grMngr = gm;
    Container cpane = this.getContentPane();
    GridBagLayout gridBag = new GridBagLayout();
    GridBagConstraints constraints = new GridBagConstraints();
    cpane.setLayout(gridBag);
    constraints.fill=GridBagConstraints.HORIZONTAL;
    constraints.anchor=GridBagConstraints.WEST;
    JLabel lb1 = new JLabel("Command line (use %s for source and %t for target)");
    buildConstraints(constraints, 0, 0, 2, 1, 70, 15);
    gridBag.setConstraints(lb1, constraints);
    cpane.add(lb1);
    constraints.fill=GridBagConstraints.NONE;
    constraints.anchor=GridBagConstraints.EAST;
    JButton helpBt = new JButton("?");
    buildConstraints(constraints, 2, 0, 1, 1, 30, 0);
    gridBag.setConstraints(helpBt, constraints);
    cpane.add(helpBt);
    ActionListener a0=new ActionListener(){
        public void actionPerformed(ActionEvent e){
            JOptionPane.showMessageDialog(CallBox.this, Messages.customCallHelp);
        }
        };
    helpBt.addActionListener(a0);
    constraints.fill=GridBagConstraints.HORIZONTAL;
    constraints.anchor=GridBagConstraints.WEST;
    cmdLineCbb = new JComboBox(ConfigManager.LAST_COMMANDS);
    cmdLineCbb.setEditable(true);
    cmdLineCbb.setMaximumRowCount(ConfigManager.COMMAND_LIMIT);
    buildConstraints(constraints, 0, 1, 3, 1, 100, 23);
    gridBag.setConstraints(cmdLineCbb, constraints);
    cpane.add(cmdLineCbb);
    JLabel lb2 = new JLabel("Source file");
    buildConstraints(constraints, 0, 2, 3, 1, 100, 15);
    gridBag.setConstraints(lb2, constraints);
    cpane.add(lb2);
    srcFileTf = new JTextField();
    buildConstraints(constraints, 0, 3, 2, 1, 70, 23);
    gridBag.setConstraints(srcFileTf, constraints);
    cpane.add(srcFileTf);
    constraints.fill=GridBagConstraints.NONE;
    constraints.anchor=GridBagConstraints.EAST;
    brwBt = new JButton("Browse...");
    buildConstraints(constraints, 2, 3, 1, 1, 30, 0);
    gridBag.setConstraints(brwBt, constraints);
    cpane.add(brwBt);
    cancelBt = new JButton("Cancel");
    buildConstraints(constraints, 0, 4, 2, 1, 70, 24);
    gridBag.setConstraints(cancelBt, constraints);
    cpane.add(cancelBt);
    constraints.anchor=GridBagConstraints.WEST;
    openBt = new JButton("Open");
    buildConstraints(constraints, 2, 4, 1, 1, 30, 0);
    gridBag.setConstraints(openBt, constraints);
    cpane.add(openBt);
    brwBt.addActionListener(this);
    openBt.addActionListener(this);
    cancelBt.addActionListener(this);
    //window
    WindowListener w0=new WindowAdapter(){
        public void windowClosing(WindowEvent e){
            dispose();
        }
        };
    this.addWindowListener(w0);
    this.setTitle("Open");
    this.setSize(FRAME_WIDTH, FRAME_HEIGHT);
    this.setLocationRelativeTo(grMngr.mainView.getFrame());
    this.setResizable(false);
    this.setVisible(true);
    cmdLineCbb.getEditor().getEditorComponent().requestFocus();
    }

    void chooseSourceFile(){
    JFileChooser fc = new JFileChooser(ConfigManager.m_LastDir!=null ? ConfigManager.m_LastDir : ConfigManager.m_PrjDir);
    fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
    fc.setDialogTitle("Find Source File");
    int returnVal= fc.showOpenDialog(this);
    if (returnVal == JFileChooser.APPROVE_OPTION){
        File f = fc.getSelectedFile();
        if (f.exists()){
        ConfigManager.m_LastDir = f.getParentFile();
        srcFileTf.setText(f.getAbsolutePath());
        }
    }
    }

    void execCommand(){
    final String cmd = CMD_LINE;
    if (cmd .indexOf("%s") != -1 && cmd.indexOf("%t") != -1){
        if (srcFileTf.getText() != null && srcFileTf.getText().length() > 0){
        final SwingWorker worker=new SwingWorker(){
            public Object construct(){
                setVisible(false);
                application.gvLdr.load(cmd, srcFileTf.getText());
                dispose();
                return null;
            }
            };
        worker.start();
        }
        else {
        JOptionPane.showMessageDialog(this, Messages.customCallFileError, "Source file not specified", JOptionPane.ERROR_MESSAGE);
        }
    }
    else {
        JOptionPane.showMessageDialog(this, Messages.customCallExprError, "Ill-formed command line", JOptionPane.ERROR_MESSAGE);
    }
    }

    public void actionPerformed(ActionEvent e){
    Object o = e.getSource();
    if (o == brwBt){
        chooseSourceFile();
    }
    else if (o == openBt){
        CMD_LINE = (String)cmdLineCbb.getSelectedItem();
        application.cfgMngr.rememberCommandLine(CMD_LINE);
        execCommand();
    }
    else if (o == cancelBt){
        this.setVisible(false);
        this.dispose();
    }
    }

    static void buildConstraints(GridBagConstraints gbc, int gx,int gy,int gw,int gh,int wx,int wy){
    gbc.gridx=gx;
    gbc.gridy=gy;
    gbc.gridwidth=gw;
    gbc.gridheight=gh;
    gbc.weightx=wx;
    gbc.weighty=wy;
    }

}
