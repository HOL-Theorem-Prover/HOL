/*   FILE: ZGRApplet.java
 *   DATE OF CREATION:   Fri May 09 09:52:34 2003
 *   Copyright (c) 2003 World Wide Web Consortium. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: ZGRApplet.java 4961 2013-05-30 20:39:29Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.AlphaComposite;
import java.awt.Dimension;
import java.awt.Rectangle;
import java.awt.Container;
import java.awt.BorderLayout;
import java.awt.GridBagLayout;
import java.awt.GridBagConstraints;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseMotionAdapter;
import java.awt.event.KeyAdapter;
import javax.swing.JApplet;
import javax.swing.JPanel;
import javax.swing.JLabel;
import javax.swing.JComponent;
import javax.swing.JOptionPane;
import javax.swing.BorderFactory;

import java.util.Vector;

import java.net.URL;
import java.net.MalformedURLException;

import fr.inria.zvtm.engine.Location;
import fr.inria.zvtm.event.RepaintListener;

import org.w3c.dom.Document;

import fr.inria.zvtm.engine.*;
import fr.inria.zvtm.svg.SVGReader;


public class ZGRApplet extends JApplet implements MouseListener, KeyListener, ZGRApplication, RepaintListener {

    static final int DEFAULT_VIEW_WIDTH = 640;
    static final int DEFAULT_VIEW_HEIGHT = 480;
    static final String APPLET_WIDTH_PARAM = "width";
    static final String APPLET_HEIGHT_PARAM = "height";
    static final String SVG_FILE_URL_PARAM = "svgURL";
    static final String SHOW_NAVIGATION_CONTROLS_PARAM = "showNavControls";
    static final String SHOW_FC_PALETTE_PARAM = "showFCPalette";
    static final String APPLET_TITLE_PARAM = "title";
    static final String APPLET_BKG_COLOR_PARAM = "appletBackgroundColor";
    static final String GRAPH_BKG_COLOR_PARAM = "graphBackgroundColor";
    static final String HIGHLIGHT_COLOR_PARAM = "highlightColor";
    static final String CURSOR_COLOR_PARAM = "cursorColor";
    static final String CENTER_ON_LABEL_PARAM = "centerOnLabel";
    static final String ANTIALIASING_PARAM = "antialiased";
    static final String DISPLAY_OVERVIEW_PARAM = "displayOverview";
    static final String FOCUS_NODE_MAG_FACTOR_PARAM = "focusNodeMagFactor";

    static final String HTTP_PROTOCOL = "http://";
    static final String HTTPS_PROTOCOL = "https://";
    static final String FTP_PROTOCOL = "ftp:/";
    static final String FILE_PROTOCOL = "file:/";
    static final String JAVASCRIPT_PROTOCOL = "javascript:";
    static final String HREF_TARGET_PARAM = "target";

    String APPLET_TITLE = "ZGRViewer - Applet";

    static ConfigManager cfgMngr;

    public GVLoader gvLdr;
    public GraphicsManager grMngr;

    ZgrAppletEvtHdlr meh;

    JPanel viewPanel;
    NavPanel navPanel;
    JLabel statusBar;

    int appletWindowWidth = DEFAULT_VIEW_WIDTH;
    int appletWindowHeight = DEFAULT_VIEW_HEIGHT;

    ZGRAGlassPane gp;

    public ZGRApplet(){
        getRootPane().putClientProperty("defeatSystemEventQueueCheck", Boolean.TRUE);
    }

    public boolean exitVMonClose(){
        return false;
    }

    public void init(){
        initConfig();
        initGUI();
    }

    void initConfig(){
        grMngr = new GraphicsManager(this);
        cfgMngr = new ConfigManager(grMngr, true);
        grMngr.setConfigManager(cfgMngr);
        gvLdr = new GVLoader(this, grMngr, cfgMngr, null);
    }

    void initGUI(){
        this.addKeyListener(this);
        this.addMouseListener(this);
        // get width and height of applet panel
        try {appletWindowWidth = Integer.parseInt(getParameter(APPLET_WIDTH_PARAM));}
        catch(NumberFormatException ex){appletWindowWidth = DEFAULT_VIEW_WIDTH;}
        try {appletWindowHeight = Integer.parseInt(getParameter(APPLET_HEIGHT_PARAM));}
        catch(NumberFormatException ex){appletWindowHeight = DEFAULT_VIEW_HEIGHT;}
        // should the navigation control panel be displayed or not
        boolean showNavControl = true;
        try {
            String s = getParameter(SHOW_NAVIGATION_CONTROLS_PARAM);
            if (s != null){
                showNavControl = (new Boolean(s)).booleanValue();
            }
        }
        catch(Exception ex){showNavControl = true;}
        boolean showFCPalette = true;
        try {
            String s = getParameter(SHOW_FC_PALETTE_PARAM);
            if (s != null){
                showFCPalette = (new Boolean(s)).booleanValue();
            }
        }
        catch(Exception ex){showFCPalette = true;}
        boolean showOverview = true;
        try {
            String s = getParameter(DISPLAY_OVERVIEW_PARAM);
            if (s != null){
                showOverview = (new Boolean(s)).booleanValue();
            }
        }
        catch(Exception ex){showOverview = true;}
        try {
            APPLET_TITLE = getParameter(APPLET_TITLE_PARAM);
        }
        catch(Exception ex){APPLET_TITLE = "ZGRViewer - Applet";}
        Color APPLET_BKG_COLOR = null;
        try {
            APPLET_BKG_COLOR = SVGReader.getColor(getParameter(APPLET_BKG_COLOR_PARAM));
        }
        catch(Exception ex){}
        Color CURSOR_COLOR = null;
        try {
            CURSOR_COLOR = SVGReader.getColor(getParameter(CURSOR_COLOR_PARAM));
        }
        catch(Exception ex){}
        boolean graphBkgColorSpecified = false;
        try {
            cfgMngr.backgroundColor = SVGReader.getColor(getParameter(GRAPH_BKG_COLOR_PARAM));
            graphBkgColorSpecified = true;
        }
        catch(Exception ex){
            cfgMngr.backgroundColor = Color.WHITE;
            graphBkgColorSpecified = false;
        }
        final boolean graphBkgColorSpecifiedF = graphBkgColorSpecified;
        String centerOnLabel = null;
        try {
            centerOnLabel = getParameter(CENTER_ON_LABEL_PARAM);
        }
        catch (Exception ex){
            centerOnLabel = null;
        }
        final String centerOnLabelF = centerOnLabel;
        boolean antialiased = true;
        try {
            String s = getParameter(ANTIALIASING_PARAM);
            if (s != null){
                antialiased = (new Boolean(s)).booleanValue();
            }
        }
        catch(Exception ex){antialiased = true;}
        try {
            String s = getParameter(HIGHLIGHT_COLOR_PARAM);
            if (s != null){
                ConfigManager.HIGHLIGHT_COLOR = SVGReader.getColor(s);
            }
        }
        catch(Exception ex){ConfigManager.HIGHLIGHT_COLOR = Color.RED;}
        try {
            String s = getParameter(FOCUS_NODE_MAG_FACTOR_PARAM);
            if (s != null){
                ConfigManager.MAG_FACTOR = Float.parseFloat(s);
            }
        }
        catch(Exception ex){ConfigManager.MAG_FACTOR = 2.0f;}
        AppletUtils.initLookAndFeel();
        Container cpane = getContentPane();
        this.setSize(appletWindowWidth-10, appletWindowHeight-10);
        cpane.setSize(appletWindowWidth, appletWindowHeight);
        cpane.setBackground(APPLET_BKG_COLOR);
        viewPanel = grMngr.createPanelView(grMngr.createZVTMelements(true), appletWindowWidth, appletWindowHeight-40);
        meh = new ZgrAppletEvtHdlr(this, this.grMngr);
        grMngr.parameterizeView(meh);
        viewPanel.setPreferredSize(new Dimension(appletWindowWidth-10, appletWindowHeight-40));
        grMngr.mainView.setAntialiasing(antialiased);
        statusBar = new JLabel(Messages.EMPTY_STRING);
        JPanel borderPanel = new JPanel();
        borderPanel.setLayout(new BorderLayout());
        borderPanel.add(viewPanel, BorderLayout.CENTER);
        borderPanel.add(statusBar, BorderLayout.SOUTH);
        borderPanel.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(Color.black, 1), APPLET_TITLE));
        borderPanel.setOpaque(false);
        if (showNavControl || showOverview){
            GridBagLayout gridBag = new GridBagLayout();
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.fill = GridBagConstraints.BOTH;
            constraints.anchor = GridBagConstraints.CENTER;
            cpane.setLayout(gridBag);
            buildConstraints(constraints,0,0,1,1,90,100);
            gridBag.setConstraints(borderPanel, constraints);
            cpane.add(borderPanel);
            navPanel = new NavPanel(grMngr, centerOnLabelF, showOverview);
            buildConstraints(constraints,1,0,1,1,10,0);
            gridBag.setConstraints(navPanel, constraints);
            cpane.add(navPanel);
        }
        else {
            cpane.add(borderPanel);
        }
        if (CURSOR_COLOR != null){
            grMngr.mainView.mouse.setColor(CURSOR_COLOR);
            grMngr.mainView.mouse.setHintColor(CURSOR_COLOR);
        }
        grMngr.tp.setEnabled(showFCPalette);
        gp = new ZGRAGlassPane(appletWindowWidth, appletWindowHeight);
        this.setGlassPane(gp);
        gp.setVisible(true);
        gp.setMessage(Messages.LOADING_SVG);
        final SwingWorker worker = new SwingWorker(){
            public Object construct(){
                sleep(1000);
                requestFocus();
                grMngr.vsm.repaint();
                URL svgUrl = null;
                try {
                    svgUrl = new URL(getDocumentBase(), getParameter(SVG_FILE_URL_PARAM));
                }
                catch (MalformedURLException e) {
                    //TODO
                    e.printStackTrace();
                }
                gvLdr.loadSVG(svgUrl.toString());
                // override SVG's background color if background color is specified in applet params
                if (graphBkgColorSpecifiedF){grMngr.mainView.setBackgroundColor(cfgMngr.backgroundColor);}
                grMngr.tp.updateHiddenPosition();
                grMngr.vsm.repaint(grMngr.mainView, ZGRApplet.this);
                while (!ZGRApplet.this.paintedAtLeastOnce){
                    sleep(500);
                }
                if (centerOnLabelF != null){
                    grMngr.search(centerOnLabelF, 1);
                }
                grMngr.vsm.repaint();
                gp.setVisible(false);
                return null;
            }

            public void finished(){
                setStatusBarText(Messages.SPACE_STRING);
                viewPanel.requestFocus();
            }

        };
        worker.start();
    }

    boolean paintedAtLeastOnce = false;

    public void viewRepainted(View v){
        paintedAtLeastOnce = true;
        v.removeRepaintListener();
    }

    public void setStatusBarText(String s){
        statusBar.setText(s);
    }

    //open up the default or user-specified browser (netscape, ie,...) and try to display the content uri
    void displayURLinBrowser(String uri){
        String target = getParameter(HREF_TARGET_PARAM);
        // always reset target for javascript: protocol
        if (uri.startsWith(JAVASCRIPT_PROTOCOL)) {
            target = ConfigManager._SELF;
        }
        // make sure we have a target if not previously set
        if (target == null) target = ConfigManager._BLANK;
        try {
            URL displayUrl;
            if (!(uri.startsWith(JAVASCRIPT_PROTOCOL) ||
                uri.startsWith(HTTP_PROTOCOL) || uri.startsWith(HTTPS_PROTOCOL) ||
                uri.startsWith(FTP_PROTOCOL) || uri.startsWith(FILE_PROTOCOL))){
                // relative URL, prepend document base
                displayUrl = new URL(getDocumentBase(), uri);
            }
            else {
                displayUrl = new URL(uri);
            }
            getAppletContext().showDocument(displayUrl, target);
        }
        catch(MalformedURLException ex){System.out.println("Error: could not load "+uri);}
    }

    public void about(){
        JOptionPane.showMessageDialog(this, Messages.about);
    }

    /* Key listener (keyboard events are not sent to ViewEventHandler when View is a JPanel...) */

    public void keyPressed(KeyEvent e){
        int code = e.getKeyCode();
        char c = e.getKeyChar();
        if (code == KeyEvent.VK_PAGE_UP){grMngr.getHigherView();}
        else if (code == KeyEvent.VK_PAGE_DOWN){grMngr.getLowerView();}
        else if (code == KeyEvent.VK_HOME){grMngr.getGlobalView();}
        else if (code == KeyEvent.VK_UP){grMngr.translateView(GraphicsManager.MOVE_DOWN);}
        else if (code == KeyEvent.VK_DOWN){grMngr.translateView(GraphicsManager.MOVE_UP);}
        else if (code == KeyEvent.VK_LEFT){grMngr.translateView(GraphicsManager.MOVE_RIGHT);}
        else if (code == KeyEvent.VK_RIGHT){grMngr.translateView(GraphicsManager.MOVE_LEFT);}
        else if (c == '+'){
            if (grMngr.lensType != GraphicsManager.NO_LENS && grMngr.lens != null){
                grMngr.magnifyFocus(GraphicsManager.WHEEL_MM_STEP, grMngr.lensType, grMngr.mainCamera);

            }
            else if (meh.inZoomWindow){
                meh.tfactor = (grMngr.dmCamera.focal+Math.abs(grMngr.dmCamera.altitude))/grMngr.dmCamera.focal;
                grMngr.dmCamera.altitudeOffset(-meh.tfactor*BaseEventHandler.WHEEL_ZOOMIN_FACTOR);
                grMngr.updateMagWindow();
                grMngr.vsm.repaint();
            }
            else {
                meh.tfactor = (grMngr.mainCamera.focal+Math.abs(grMngr.mainCamera.altitude))/grMngr.mainCamera.focal;
                grMngr.mainCamera.altitudeOffset(-meh.tfactor*BaseEventHandler.WHEEL_ZOOMIN_FACTOR);
                grMngr.cameraMoved(null, null, 0);
            }
        }
        else if (c == '-'){
            if (grMngr.lensType != GraphicsManager.NO_LENS && grMngr.lens != null){
                grMngr.magnifyFocus(-GraphicsManager.WHEEL_MM_STEP, grMngr.lensType, grMngr.mainCamera);
            }
            else if (meh.inZoomWindow){
                meh.tfactor = (grMngr.dmCamera.focal+Math.abs(grMngr.dmCamera.altitude))/grMngr.dmCamera.focal;
                grMngr.dmCamera.altitudeOffset(meh.tfactor*BaseEventHandler.WHEEL_ZOOMOUT_FACTOR);
                grMngr.updateMagWindow();
                grMngr.vsm.repaint();
            }
            else {
                meh.tfactor = (grMngr.mainCamera.focal+Math.abs(grMngr.mainCamera.altitude))/grMngr.mainCamera.focal;
                grMngr.mainCamera.altitudeOffset(meh.tfactor*BaseEventHandler.WHEEL_ZOOMOUT_FACTOR);
                grMngr.cameraMoved(null, null, 0);
            }
        }
    }

    public void keyReleased(KeyEvent e){}

    public void keyTyped(KeyEvent e){}

    public void mouseClicked(MouseEvent e){}

    public void mouseEntered(MouseEvent e){}

    public void mouseExited(MouseEvent e){}

    public void mousePressed(MouseEvent e){}

    public void mouseReleased(MouseEvent e){}

    static void buildConstraints(GridBagConstraints gbc, int gx,int gy,int gw,int gh,int wx,int wy){
        gbc.gridx = gx;
        gbc.gridy = gy;
        gbc.gridwidth = gw;
        gbc.gridheight = gh;
        gbc.weightx = wx;
        gbc.weighty = wy;
    }

}

class ZGRAGlassPane extends JComponent {

    static final AlphaComposite GLASS_ALPHA = AlphaComposite.getInstance(AlphaComposite.SRC_OVER, 0.65f);
    static final Color MSG_COLOR = Color.DARK_GRAY;

    String msg = Messages.EMPTY_STRING;
    int msgX = 0;
    int msgY = 0;

    int w,h;

    ZGRAGlassPane(int w, int h){
        super();
        this.w = w;
        this.h = h;
        addMouseListener(new MouseAdapter(){});
        addMouseMotionListener(new MouseMotionAdapter(){});
        addKeyListener(new KeyAdapter(){});
    }

    void setMessage(String m){
        msg = m;
        msgX = w/2-100;
        msgY = h/2;
        repaint(msgX, msgY-50, 200, 70);
    }

    protected void paintComponent(Graphics g){
        Graphics2D g2 = (Graphics2D)g;
        Rectangle clip = g.getClipBounds();
        g2.setComposite(GLASS_ALPHA);
        g2.setColor(Color.WHITE);
        g2.fillRect(clip.x, clip.y, clip.width, clip.height);
        g2.setComposite(AlphaComposite.Src);
        if (msg != Messages.EMPTY_STRING){
            g2.setColor(MSG_COLOR);
            g2.setFont(ConfigManager.defaultFont);
            g2.drawString(msg, msgX, msgY);
        }
    }

}
