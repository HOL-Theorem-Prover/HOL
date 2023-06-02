/*   FILE: TextViewer.java
 *   DATE OF CREATION:   Wed Dec 03 09:31:46 2003
 *   Copyright (c) Emmanuel Pietriga, 2002. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: TextViewer.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Container;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.HierarchyEvent;
import java.awt.event.HierarchyListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

/*A simple text viewer that displays the content of a stringbuffer. Can be set to automatically update its content periodically. Can be used for showing error logs, raw source files,...*/

public class TextViewer extends JFrame implements ActionListener,KeyListener,Runnable {

    Thread runView;

    JButton okBt;
    JButton clearBt;

    StringBuffer text;
    int oldSize;

    int period;

    JTextArea ar;

    /**
     *@param msgs text displayed in main area
     *@param frameTitle string appearing in window title bar
     *@param d periodic update (in milliseconds) of the main area w.r.t msgs (0=no update)
     *@param clear show a clear button in addition to the OK button
     */
    public TextViewer(StringBuffer msgs,String frameTitle,int d,boolean clear){
    text=msgs;
    oldSize=text.length();
    period=d;
    ar=new JTextArea(text.toString());
    ar.setFont(ConfigManager.defaultFont);
    ar.setEditable(false);
    ar.setLineWrap(true);
    JScrollPane sp=new JScrollPane(ar);
    sp.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
    //sp.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS);
    Container cpane=this.getContentPane();
    GridBagLayout gridBag=new GridBagLayout();
    GridBagConstraints constraints=new GridBagConstraints();
    constraints.fill=GridBagConstraints.BOTH;
    constraints.anchor=GridBagConstraints.CENTER;
    cpane.setLayout(gridBag);
    buildConstraints(constraints,0,0,2,1,100,98);
    gridBag.setConstraints(sp,constraints);
    cpane.add(sp);
    if (clear){
        okBt=new JButton("OK");
        okBt.addActionListener(this);okBt.addKeyListener(this);
        constraints.anchor=GridBagConstraints.EAST;
        constraints.fill=GridBagConstraints.NONE;
        buildConstraints(constraints,0,1,1,1,50,2);
        gridBag.setConstraints(okBt,constraints);
        cpane.add(okBt);
        clearBt=new JButton("Clear");
        clearBt.addActionListener(this);clearBt.addKeyListener(this);
        constraints.anchor=GridBagConstraints.WEST;
        buildConstraints(constraints,1,1,1,1,50,0);
        gridBag.setConstraints(clearBt,constraints);
        cpane.add(clearBt);
    }
    else {
        okBt=new JButton("OK");
        okBt.addActionListener(this);okBt.addKeyListener(this);
        constraints.anchor=GridBagConstraints.CENTER;
        constraints.fill=GridBagConstraints.HORIZONTAL;
        buildConstraints(constraints,0,1,2,1,100,2);
        gridBag.setConstraints(okBt,constraints);
        cpane.add(okBt);
    }
    WindowListener w0=new WindowAdapter(){
        public void windowClosing(WindowEvent e){stop();dispose();}
        };
    this.addWindowListener(w0);
    this.setTitle(frameTitle);
    this.pack();
    this.setLocation(0,0);
    this.setSize(700,300);
    this.setVisible(true);
    okBt.requestFocus();
    if (period>0){
        addHierarchyListener(
        new HierarchyListener() {
            public void hierarchyChanged(HierarchyEvent e) {
            if (isShowing()) {
                start();
            } else {
                stop();
            }
            }
        }
        );
        start();
    }
    }

    /**
     *@param msgs text displayed in main area
     *@param frameTitle string appearing in window title bar
     *@param d periodic update (in milliseconds) of the main area w.r.t msgs (0=no update)
     *@param x position of top-left corner
     *@param y position of top-left corner
     *@param width frame width
     *@param height frame height
     *@param clear show a clear button in addition to the OK button
     */
    public TextViewer(StringBuffer msgs,String frameTitle,int d,int x,int y,int width,int height,boolean clear){
    text=msgs;
    oldSize=text.length();
    period=d;
    ar=new JTextArea(text.toString());
    ar.setFont(ConfigManager.defaultFont);
    ar.setEditable(false);
    ar.setLineWrap(true);
    ar.setWrapStyleWord(true);
    JScrollPane sp=new JScrollPane(ar);
    sp.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
    //sp.setHorizontalScrollBarPolicy(JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS);
    Container cpane=this.getContentPane();
    GridBagLayout gridBag=new GridBagLayout();
    GridBagConstraints constraints=new GridBagConstraints();
    constraints.fill=GridBagConstraints.BOTH;
    constraints.anchor=GridBagConstraints.CENTER;
    cpane.setLayout(gridBag);
    buildConstraints(constraints,0,0,2,1,100,98);
    gridBag.setConstraints(sp,constraints);
    cpane.add(sp);
    if (clear){
        okBt=new JButton("OK");
        okBt.addActionListener(this);okBt.addKeyListener(this);
        constraints.anchor=GridBagConstraints.EAST;
        constraints.fill=GridBagConstraints.NONE;
        buildConstraints(constraints,0,1,1,1,50,2);
        gridBag.setConstraints(okBt,constraints);
        cpane.add(okBt);
        clearBt=new JButton("Clear");
        clearBt.addActionListener(this);clearBt.addKeyListener(this);
        constraints.anchor=GridBagConstraints.WEST;
        buildConstraints(constraints,1,1,1,1,50,0);
        gridBag.setConstraints(clearBt,constraints);
        cpane.add(clearBt);
    }
    else {
        okBt=new JButton("OK");
        okBt.addActionListener(this);okBt.addKeyListener(this);
        constraints.anchor=GridBagConstraints.CENTER;
        constraints.fill=GridBagConstraints.HORIZONTAL;
        buildConstraints(constraints,0,1,2,1,100,2);
        gridBag.setConstraints(okBt,constraints);
        cpane.add(okBt);
    }
    WindowListener w0=new WindowAdapter(){
        public void windowClosing(WindowEvent e){stop();dispose();}
        };
    this.addWindowListener(w0);
    this.setTitle(frameTitle);
    this.pack();
    this.setLocation(x,y);
    this.setSize(width,height);
    this.setVisible(true);
    okBt.requestFocus();
    if (period>0){
        addHierarchyListener(
        new HierarchyListener() {
            public void hierarchyChanged(HierarchyEvent e) {
            if (isShowing()) {
                start();
            } else {
                stop();
            }
            }
        }
        );
        start();
    }
    }

    public void start() {
    runView = new Thread(this);
    runView.setPriority(Thread.MIN_PRIORITY);
    runView.start();
    }

    public synchronized void stop() {
    runView = null;
    notify();
    }

    public void run() {
    Thread me = Thread.currentThread();
    while (runView==me){
        if (text.length()!=oldSize){ar.setText(text.toString());}  //update text only if new error messages
        oldSize=text.length();
        try {
        runView.sleep(period);
        }
        catch (InterruptedException e) {}
    }
    }


    public void actionPerformed(ActionEvent e){
    if (e.getSource()==okBt){this.stop();this.dispose();}
    else if (e.getSource()==clearBt){text.setLength(0);ar.setText("");}
    }

    public void keyPressed(KeyEvent e){
    if (e.getKeyCode()==KeyEvent.VK_ENTER){
        if (e.getSource()==okBt){this.stop();this.dispose();}
        else if (e.getSource()==clearBt){text.setLength(0);ar.setText("");}
    }
    }

    public void keyReleased(KeyEvent e){}
    public void keyTyped(KeyEvent e){}

    void buildConstraints(GridBagConstraints gbc, int gx,int gy,int gw,int gh,int wx,int wy){
    gbc.gridx=gx;
    gbc.gridy=gy;
    gbc.gridwidth=gw;
    gbc.gridheight=gh;
    gbc.weightx=wx;
    gbc.weighty=wy;
    }

}
