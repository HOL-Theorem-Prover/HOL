/*   FILE: PeriodicActionManager.java
 *   DATE OF CREATION:   Thu Jan 09 14:14:35 2003
 *   Copyright (c) Emmanuel Pietriga, 2002. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: PeriodicActionManager.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Color;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Toolkit;
import java.awt.Graphics2D;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionListener;
import java.awt.geom.Rectangle2D;

import fr.inria.zvtm.glyphs.VText;
import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.svg.Metadata;
import fr.inria.zvtm.engine.Java2DPainter;

class PeriodicActionManager implements Runnable, MouseMotionListener, Java2DPainter {

    static int SLEEP_TIME = 500;  // check for tooltip changes every 1.0s
    static int TOOLTIP_TIME = 1000; // tooltip info should appear only if mouse is idle for at least 1.5s

    static Color TP_BACKGROUND = new Color(255, 255, 147);
    static Color TP_FOREGROUND = Color.black;
    static Font TP_FONT = new Font("Dialog", Font.PLAIN, 10);
    static int TP_PADDING = 4;
    static int TP_MARGIN = 15;
    private boolean invalidBounds = true;

    GraphicsManager grMngr;

    Thread runTP;

    long lastMouseMoved = System.currentTimeMillis();

    Glyph tippedGlyph;
    String tipLabel;
    int lX, lY, rX, rY, rW, rH;


    boolean updatePalette = false;

    PeriodicActionManager(GraphicsManager gm){
    this.grMngr = gm;
    }

    public void start(){
    runTP = new Thread(this);
    runTP.setPriority(Thread.MIN_PRIORITY);
    runTP.start();
    }

    public synchronized void stop() {
    runTP = null;
    notify();
    }

    public void run(){
    Thread me = Thread.currentThread();
    while (runTP == me) {
        updateTooltip();
        checkToolPalette();
        try {
        runTP.sleep(SLEEP_TIME);   //sleep ... ms
        }
        catch (InterruptedException e) {
        return;
        }
    }
    }

    void updateTooltip(){
    if ((System.currentTimeMillis()-lastMouseMoved) > TOOLTIP_TIME){
        Glyph g = grMngr.mainView.getPanel().lastGlyphEntered();
        if (g != null && g != grMngr.boundingBox && tippedGlyph != g){
        tippedGlyph = g;
        if (tippedGlyph.getOwner() != null && tippedGlyph.getOwner() instanceof LElem){
            tipLabel = ((LElem)tippedGlyph.getOwner()).getTooltip(tippedGlyph);
        }
        if (tipLabel != null && tipLabel.length() > 0){
            lX = grMngr.mainView.mouse.getPanelXCoordinate() + TP_MARGIN;
            lY = grMngr.mainView.mouse.getPanelYCoordinate() + TP_MARGIN;
            invalidBounds = true;
            grMngr.vsm.repaint();
        }
        }
    }
    }

    void removeTooltip(){
    tipLabel = null;
    tippedGlyph = null;
    invalidBounds = true;
    grMngr.vsm.repaint();
    }

    void computeTipRectangle(int labelWidth, int labelHeight){
    rX = lX - TP_PADDING;
    rY = lY - labelHeight;
    rW = labelWidth + TP_PADDING + TP_PADDING;
    rH = labelHeight + TP_PADDING;
    }

    public void paint(Graphics2D g2d, int viewWidth, int viewHeight){
    if (tipLabel != null){
        Font origFont = g2d.getFont();
        g2d.setFont(TP_FONT);
        if (invalidBounds){
        Rectangle2D r2d = g2d.getFontMetrics().getStringBounds(tipLabel, g2d);
        computeTipRectangle((int)r2d.getWidth(), (int)r2d.getHeight());
        invalidBounds = false;
        }
        g2d.setColor(TP_BACKGROUND);
        g2d.fillRect(rX, rY, rW, rH);
        g2d.setColor(TP_FOREGROUND);
        g2d.drawRect(rX, rY, rW, rH);
        g2d.drawString(tipLabel, lX, lY);
        g2d.setFont(origFont);
    }
    }

    public void mouseDragged(MouseEvent e){
    lastMouseMoved = System.currentTimeMillis();
    removeTooltip();
    }

    public void mouseMoved(MouseEvent e){
    lastMouseMoved = System.currentTimeMillis();
    removeTooltip();
    }

    void requestToolPaletteRelocation(){
    updatePalette = true;
    }

    void checkToolPalette(){
    if (updatePalette){
        grMngr.tp.updateHiddenPosition();
        updatePalette = false;
    }
    }

}
