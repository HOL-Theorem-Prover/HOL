/*   FILE: ZgrvEvtHdlr.java
 *   DATE OF ORIGINAL CREATION:   Thu Jan 09 15:18:48 2003
 *   Copyright (c) 2003 World Wide Web Consortium. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2013. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 *   $Id: ZgrvEvtHdlr.java 4943 2013-02-21 17:49:54Z epietrig $
 */

 //edited by haoyang
package net.claribole.zgrviewer;

import java.awt.Graphics2D;
import java.awt.Color;
import java.awt.Cursor;
import java.awt.Desktop;
import java.awt.Font;
import java.awt.Point;
import java.util.ArrayList;
import java.util.Vector;
import static java.nio.charset.StandardCharsets.*;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;

import fr.inria.zvtm.glyphs.VText;
import haoyang.FileReader;
import haoyang.TheoremParser;
import haoyang.Theory;
import haoyang.messageBox;
//import fr.inria.zvtm.engine.AnimManager;
import fr.inria.zvtm.engine.Camera;
import fr.inria.zvtm.engine.SwingWorker;
import fr.inria.zvtm.engine.VCursor;
import fr.inria.zvtm.engine.View;
import fr.inria.zvtm.engine.ViewPanel;
import fr.inria.zvtm.engine.VirtualSpace;
import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.glyphs.DPath;
import fr.inria.zvtm.glyphs.VSegment;
import fr.inria.zvtm.glyphs.VImage;
import fr.inria.zvtm.glyphs.VText;
import fr.inria.zvtm.event.ViewListener;
import fr.inria.zvtm.engine.portals.Portal;
import fr.inria.zvtm.animation.Animation;
import fr.inria.zvtm.animation.interpolation.IdentityInterpolator;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.MouseEvent;
import java.awt.event.MouseWheelEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class ZgrvEvtHdlr extends BaseEventHandler implements ViewListener {

    protected ZGRViewer application;
    StringBuffer theoryname=new StringBuffer();

    protected ZgrvEvtHdlr(ZGRViewer app, GraphicsManager gm){
        this.application = app;
        this.grMngr = gm;
    }

    public void press1(ViewPanel v,int mod,int jpx,int jpy, MouseEvent e){
        
        if (toolPaletteIsActive){return;}
        lastJPX = jpx;
        lastJPY = jpy;
        Glyph g = v.lastGlyphEntered();
        if (inZoomWindow){
            if (grMngr.dmPortal.coordInsideBar(jpx, jpy)){
                draggingZoomWindow = true;
            }
            else {
                draggingZoomWindowContent = true;
            }
        }
        else if (inMagWindow){
            v.getVCursor().stickGlyph(grMngr.magWindow);
            draggingMagWindow = true;
        }
        else if (grMngr.tp.isBringAndGoMode() && g != null){
            grMngr.startBringAndGo(g);
        }
        else if (grMngr.tp.isLinkSlidingMode()){
            Point location = e.getComponent().getLocationOnScreen();
            relative = e.getPoint();
            LS_SX = v.getVCursor().getVSXCoordinate();
            LS_SY = v.getVCursor().getVSYCoordinate();
            grMngr.attemptLinkSliding(LS_SX, LS_SY, location.x, location.y);
        }
        else if (grMngr.tp.isEditMode()){
            pressInEditMode(g, v.getVCursor(), grMngr.mainCamera, mod);
        }
        else {
            grMngr.rememberLocation(v.cams[0].getLocation());
            if (mod == NO_MODIFIER || mod == SHIFT_MOD || mod == META_MOD || mod == META_SHIFT_MOD){
                manualLeftButtonMove=true;
                lastJPX=jpx;
                lastJPY=jpy;
                v.getVCursor().setSensitivity(false);
                activeCam=grMngr.vsm.getActiveCamera();
            }
            else if (mod == ALT_MOD){
                zoomingInRegion=true;
                x1=v.getVCursor().getVSXCoordinate();
                y1=v.getVCursor().getVSYCoordinate();
                v.setDrawRect(true);
            }
        }
    }

    public void release1(ViewPanel v,int mod,int jpx,int jpy, MouseEvent e){
        
        if (ConfigManager.DYNASPOT && !toolPaletteIsActive && !v.getVCursor().getDynaPicker().isDynaSpotActivated()){grMngr.activateDynaSpot(true, false);}
        if (grMngr.isBringingAndGoing){
            grMngr.endBringAndGo(v.lastGlyphEntered());
        }
        else if (grMngr.isLinkSliding){
            grMngr.endLinkSliding();
        }
        if (toolPaletteIsActive){return;}
        draggingZoomWindow = false;
        draggingZoomWindowContent = false;
        if (editingSpline || movingEdgeLabelOrBox){
            v.getVCursor().unstickLastGlyph();
            editingSpline = movingEdgeLabelOrBox = false;
        }
        else if (movingNode){
            v.getVCursor().unstickLastGlyph();
            grMngr.geom.unstickAll();
            movingNode = false;
        }
        if (draggingMagWindow){
            draggingMagWindow = false;
            v.getVCursor().unstickLastGlyph();
        }
        if (zoomingInRegion){
            v.setDrawRect(false);
            x2=v.getVCursor().getVSXCoordinate();
            y2=v.getVCursor().getVSYCoordinate();
            if ((Math.abs(x2-x1)>=4) && (Math.abs(y2-y1)>=4)){
                grMngr.mainView.centerOnRegion(grMngr.vsm.getActiveCamera(),ConfigManager.ANIM_MOVE_LENGTH,x1,y1,x2,y2);
            }
            zoomingInRegion=false;
        }
        else if (manualLeftButtonMove){
            grMngr.mainCamera.setXspeed(0);
            grMngr.mainCamera.setYspeed(0);
            grMngr.mainCamera.setZspeed(0);
            v.hideFirstOrderPanWidget();
            //v.setDrawDrag(false);
            v.getVCursor().setSensitivity(true);
            if (autoZooming){unzoom(v);}
            manualLeftButtonMove=false;
        }
    }

    public void click1(ViewPanel v,int mod,int jpx,int jpy,int clickNumber, MouseEvent e){
        
        if (toolPaletteIsActive){
            if (clickNumber == 2){return;}
            if (v.lastGlyphEntered() != null){grMngr.tp.selectMode((VImage)v.lastGlyphEntered());}
        }
        else if (mod == META_MOD){
            if (clickNumber == 2){return;}
            if (grMngr.tp.isHighlightMode() && v.getGlyphsUnderCursorList().length>0){
                Glyph g = v.lastGlyphEntered();
                grMngr.highlightElement(g, v.cams[0], v.getVCursor(), true, 0, true, -1);
            }
        }
        else {
            if (grMngr.tp.isBringAndGoMode() || grMngr.tp.isLinkSlidingMode()){return;}
            if (grMngr.tp.isFadingLensNavMode() || grMngr.tp.isProbingLensNavMode()){
                if (clickNumber == 2){return;}
                lastJPX = jpx;
                lastJPY = jpy;
                lastVX = v.getVCursor().getVSXCoordinate();
                lastVY = v.getVCursor().getVSYCoordinate();
                if (grMngr.lensType != GraphicsManager.NO_LENS){
                    grMngr.zoomInPhase2(lastVX, lastVY);
                }
                else {
                    if (cursorNearBorder){
                        // do not activate the lens when cursor is near the border
                        return;
                    }
                    grMngr.zoomInPhase1(jpx, jpy);
                }
            }
            else if (grMngr.tp.isDragMagNavMode()){
                if (clickNumber == 2){return;}
                grMngr.triggerDM(jpx, jpy, this);
            }
            else if (grMngr.tp.isEditMode()){
                return;
            }
            else {
                if (clickNumber == 2){click2(v, mod, jpx, jpy, clickNumber, e);}
                else {
                    Glyph g = v.lastGlyphEntered();
                    if (mod == SHIFT_MOD){
                        grMngr.highlightElement(g, v.cams[0], v.getVCursor(), true, 0, true, -1);
                    }
                    else {
                        if (g != null && g != grMngr.boundingBox){
                            grMngr.mainView.centerOnGlyph(g, v.cams[0], ConfigManager.ANIM_MOVE_LENGTH, true, ConfigManager.MAG_FACTOR);
                        }
                    }
                }
            }
        }
    }

    Glyph startG, endG;
    LEdge edge;

    public void press2(ViewPanel v,int mod,int jpx,int jpy, MouseEvent e){
        
        // XXXXXXXXXXXXXXX debug / test
        if (grMngr.tp.isEditMode()){
            if (startG!=null){
                endG = v.lastGlyphEntered();
                edge = grMngr.addEdge(startG, endG, "test", true);
                startG = endG = null;
            }
            else {
                startG = v.lastGlyphEntered();
            }
        }
        //else if (mod == ALT_MOD){
        //  grMngr.removeEdge(edge);
        //}
        // XXXXXXXXXXXXXXX debug / test
    }

    public void release2(ViewPanel v,int mod,int jpx,int jpy, MouseEvent e){}

    public void click2(ViewPanel v,int mod,int jpx,int jpy,int clickNumber, MouseEvent e){
        
        if (toolPaletteIsActive){return;}
        if (clickNumber == 2){return;}
        Glyph g = v.lastGlyphEntered();
        if (g!=null && g != grMngr.boundingBox){
            if (g.getOwner() != null){
                getAndDisplayURL((LElem)g.getOwner(), g);
            }
        }
        else {
            attemptDisplayEdgeURL(v.getVCursor(), v.cams[0]);
        }
    }

    public void press3(ViewPanel v,int mod,int jpx,int jpy, MouseEvent e){
        


        //this is the right-click listener!

        // if (ConfigManager.DYNASPOT){grMngr.activateDynaSpot(false, false);}
        // if (toolPaletteIsActive){return;}
        // if (grMngr.tp.isFadingLensNavMode() || grMngr.tp.isProbingLensNavMode()){
        //     lastJPX = jpx;
        //     lastJPY = jpy;
        // }
        // else {
        //     v.parent.setActiveLayer(1);
        //     application.displayMainPieMenu(true);
        // }
        
    }
        
  
    

    public void release3(ViewPanel v,int mod,int jpx,int jpy, MouseEvent e){
        
    //     if (ConfigManager.DYNASPOT){grMngr.activateDynaSpot(true, false);}
    //     if (toolPaletteIsActive){return;}
    //     Glyph g = v.getVCursor().getPicker().lastGlyphEntered();
    //     if (g != null && g.getType() == Messages.PM_ENTRY){
    //         try {
    //             application.pieMenuEvent(g);
    //         } catch (IOException | InterruptedException e1) {
    //             // TODO Auto-generated catch block
    //             e1.printStackTrace();
    //         }
    //     }
    //     if (application.mainPieMenu != null){
    //         application.displayMainPieMenu(false);
    //     }
    //     if (application.subPieMenu != null){
    //         application.displaySubMenu(null, false);
    //     }
    //     v.parent.setActiveLayer(0);
    }


    //method by haoyang
    public void click3(ViewPanel v,int mod,int jpx,int jpy,int clickNumber, MouseEvent e){
        


        Glyph g = v.lastGlyphEntered();
        //given glyph->find the inside node->get the node label
        //get the name of object!
        String objectname=grMngr.getGlyphText(g,v.cams[0], v.getVCursor());
        
        
        //the popmenu
        if(objectname!=null){
            //the theory graph mode!
            if(FileReader.status==false){
                JPopupMenu popupMenu=new JPopupMenu();
                JMenuItem sigItem=new JMenuItem("open .sig");
                JMenuItem smlItem=new JMenuItem("open .sml");
                JMenuItem themItem=new JMenuItem("theorems");
                
                popupMenu.add(sigItem);
                popupMenu.add(smlItem);
                popupMenu.add(themItem);

                GVLoader gvLdr=this.application.gvLdr;


                ActionListener a0=new ActionListener(){
                    public void actionPerformed(ActionEvent e){
                        if(e.getSource()==sigItem){

                            StringBuffer sig=new StringBuffer("");
                            //full name
                            String filename=objectname+"Theory.sig";
                            File dir = new File(FileReader.MainFolder);
                            //search sig:path
                            TheoremParser.searchFile(dir,filename,sig);
                            try {
                                String text = Files.readString(Paths.get(sig.toString()));
                                // byte[] ptext = text.getBytes(UTF_8); 
                                // String value = new String(ptext, UTF_8); 
                                messageBox m=new messageBox(text, filename);
                            } catch (IOException e1) {
                                // TODO Auto-generated catch block
                                e1.printStackTrace();
                            }
                            
                        }

                        if(e.getSource()==smlItem){

                            StringBuffer sml=new StringBuffer("");
                            //full name
                            String filename=objectname+"Script.sml";
                            File dir = new File(FileReader.MainFolder);
                            //search sig:path
                            TheoremParser.searchFile(dir,filename,sml);
                            try {
                                String text = Files.readString(Paths.get(sml.toString()));
                                messageBox m=new messageBox(text, filename);
                            } catch (IOException e1) {
                                // TODO Auto-generated catch block
                                e1.printStackTrace();
                            }
                            
                        }

                        //to genrate theorem graph-> objectname ->
                        else if (e.getSource()==themItem){
                            theoryname=new StringBuffer(objectname);
                            try {
                                gvLdr.themLoadSvg(objectname);
                            } catch (IOException | InterruptedException e1) {
                                // TODO Auto-generated catch block
                                e1.printStackTrace();
                            }
                        }

                    }
         
                };
                
                sigItem.addActionListener(a0);
                smlItem.addActionListener(a0);
                themItem.addActionListener(a0);
    
                popupMenu.show(e.getComponent(), jpx, jpy);
            }
            //FileReader.status==true: theorem graph mode
            else{

                JPopupMenu popupMenu=new JPopupMenu();
                JMenuItem sigItem=new JMenuItem("open .sig");
                JMenuItem smlItem=new JMenuItem("open .sml");
                JMenuItem externalThem=new JMenuItem("external dependency");
                
                
                popupMenu.add(sigItem);
                popupMenu.add(smlItem);
                popupMenu.add(externalThem);

                

                //theory: open .sig/.sml
                String thyname=theoryname.toString();
                System.out.println("under theory: "+thyname);

                GVLoader gvLdr=this.application.gvLdr;
                
                ActionListener a0=new ActionListener(){
                    public void actionPerformed(ActionEvent e){
                        if (e.getSource()==sigItem){
    
                            StringBuffer sig=new StringBuffer("");
                            //full name
                            String filename=thyname+"Theory.sig";
                            File dir = new File(FileReader.MainFolder);
                            //search sig:path
                            TheoremParser.searchFile(dir,filename,sig);
                            
                            try {
                                System.out.println("find path"+sig.toString());
                                String text = Files.readString(Paths.get(sig.toString()));
                                String statement=TheoremParser.sig_parser(text,objectname);
                                messageBox m=new messageBox(statement, objectname);
                            } catch (IOException e1) {
                                // TODO Auto-generated catch block
                                e1.printStackTrace();
                            }
                            
    
                        }
                        else if (e.getSource()==smlItem){
    
                            StringBuffer sml=new StringBuffer("");
                            //full name
                            String filename=thyname+"Script.sml";
                            File dir = new File(FileReader.MainFolder);
                            //search sig:path
                            TheoremParser.searchFile(dir,filename,sml);
                            
                            try {
                                System.out.println("find path"+sml.toString());
                                String provement=TheoremParser.sml_parser(sml.toString(),objectname);
                                messageBox m=new messageBox(provement, objectname);
                            } catch (IOException e1) {
                                // TODO Auto-generated catch block
                                e1.printStackTrace();
                            }
    
                        }
                        else if(e.getSource()==externalThem){
                            String text=FileReader.external.get(objectname);
                            messageBox m=new messageBox(text,"external theorems' dependency");
                        }

                    }
         
                };
                
                sigItem.addActionListener(a0);
                smlItem.addActionListener(a0);
                externalThem.addActionListener(a0);

                popupMenu.show(e.getComponent(), jpx, jpy);
            }


        }
    }



    
    public void mouseMoved(ViewPanel v,int jpx,int jpy, MouseEvent e){
        lx = jpx;
        ly = jpy;
        if ((jpx-grMngr.LENS_R1) < 0){
            lx = grMngr.LENS_R1;
            cursorNearBorder = true;
        }
        else if ((jpx+grMngr.LENS_R1) > grMngr.panelWidth){
            lx = grMngr.panelWidth - grMngr.LENS_R1;
            cursorNearBorder = true;
        }
        else {
            cursorNearBorder = false;
        }
        if ((jpy-grMngr.LENS_R1) < 0){
            ly = grMngr.LENS_R1;
            cursorNearBorder = true;
        }
        else if ((jpy+grMngr.LENS_R1) > grMngr.panelHeight){
            ly = grMngr.panelHeight - grMngr.LENS_R1;
            cursorNearBorder = true;
        }
        if (grMngr.lensType != 0 && grMngr.lens != null){
            grMngr.moveLens(lx, ly, e.getWhen());
        }
        else if (grMngr.tp.isEnabled()){
            if (grMngr.tp.insidePaletteTriggerZone(jpx, jpy)){
                if (!grMngr.tp.isShowing()){grMngr.tp.show();toolPaletteIsActive = true;}
            }
            else {
                if (grMngr.tp.isShowing()){grMngr.tp.hide();toolPaletteIsActive = false;}
            }
        }
        if (ConfigManager.DYNASPOT){
            v.getVCursor().getDynaPicker().dynaPick(grMngr.mainCamera);
        }
    }

    public void mouseDragged(ViewPanel v,int mod,int buttonNumber,int jpx,int jpy, MouseEvent e){
        if (toolPaletteIsActive || grMngr.isBringingAndGoing){return;}
        if (v.getVCursor().getDynaPicker().isDynaSpotActivated()){grMngr.activateDynaSpot(false, false);}
        if (editingSpline){
            grMngr.geom.updateEdgeSpline();
        }
        else if (movingEdgeLabelOrBox || movingNode){
            // do nothing but prevent exec of else
            return;
        }
        else if (grMngr.isLinkSliding){
            // ignore events triggered by AWT robot
            grMngr.linkSlider(v.getVCursor().getVSXCoordinate(), v.getVCursor().getVSYCoordinate(), false);
        }
        else if (mod != ALT_MOD && buttonNumber == 1){
            if (draggingZoomWindow){
                grMngr.dmPortal.move(jpx-lastJPX, jpy-lastJPY);
                lastJPX = jpx;
                lastJPY = jpy;
                grMngr.vsm.repaint();
            }
            else if (draggingZoomWindowContent){
                tfactor = (grMngr.dmCamera.focal+(grMngr.dmCamera.altitude))/grMngr.dmCamera.focal;
                synchronized(grMngr.dmCamera){
                    grMngr.dmCamera.move(Math.round(tfactor*(lastJPX-jpx)),
                        Math.round(tfactor*(jpy-lastJPY)));
                    lastJPX = jpx;
                    lastJPY = jpy;
                    grMngr.updateMagWindow();
                }
            }
            else if (draggingMagWindow){
                grMngr.updateZoomWindow();
            }
            else if (manualLeftButtonMove){
                if (!v.isShowingFirstOrderPanWidget()){
                    v.showFirstOrderPanWidget(lastJPX, lastJPY);
                }
                if (mod == SHIFT_MOD || mod == META_SHIFT_MOD){
                    grMngr.mainCamera.setXspeed(0);
                    grMngr.mainCamera.setYspeed(0);
                    grMngr.mainCamera.setZspeed((lastJPY-jpy)*ZOOM_SPEED_COEF);
                }
                else {
                    tfactor = (activeCam.focal+Math.abs(activeCam.altitude))/activeCam.focal;
                    jpxD = jpx-lastJPX;
                    jpyD = lastJPY-jpy;
                    grMngr.mainCamera.setXspeed((activeCam.altitude>0) ? jpxD*(tfactor/PAN_SPEED_FACTOR) : jpxD/(tfactor*PAN_SPEED_FACTOR));
                    grMngr.mainCamera.setYspeed((activeCam.altitude>0) ? jpyD*(tfactor/PAN_SPEED_FACTOR) : jpyD/(tfactor*PAN_SPEED_FACTOR));
                    grMngr.mainCamera.setZspeed(0);
                    if (application.cfgMngr.isSDZoomEnabled()){
                        dragValue = Math.sqrt(jpxD*jpxD + jpyD*jpyD);
                        if (!autoZooming && dragValue > application.cfgMngr.SD_ZOOM_THRESHOLD){
                            autoZooming = true;
                            Animation a = grMngr.vsm.getAnimationManager().getAnimationFactory().createCameraAltAnim(300, v.cams[0],
                                new Float(application.cfgMngr.autoZoomFactor*(v.cams[0].getAltitude()+v.cams[0].getFocal())), true,
                                IdentityInterpolator.getInstance(), null);
                            grMngr.vsm.getAnimationManager().startAnimation(a, false);
                        }
                    }
                }
            }
        }
        if (grMngr.lensType != GraphicsManager.NO_LENS && grMngr.lens != null){
            grMngr.moveLens(jpx, jpy, e.getWhen());
        }
    }

    public void mouseWheelMoved(ViewPanel v,short wheelDirection,int jpx,int jpy, MouseWheelEvent e){
        if (grMngr.lensType != GraphicsManager.NO_LENS && grMngr.lens != null){
            if (wheelDirection  == ViewListener.WHEEL_UP){
                grMngr.magnifyFocus(GraphicsManager.WHEEL_MM_STEP, grMngr.lensType, grMngr.mainCamera);
            }
            else {
                grMngr.magnifyFocus(-GraphicsManager.WHEEL_MM_STEP, grMngr.lensType, grMngr.mainCamera);
            }
        }
        else if (grMngr.tp.isHighlightMode() && v.getGlyphsUnderCursorList().length>0){
            Glyph g = v.lastGlyphEntered();
            int dir = -1;
            if (e.isShiftDown()) dir = LEdge.INCOMING;
            if (e.isControlDown()) dir = LEdge.OUTGOING;
            if (e.isShiftDown() && e.isControlDown()) dir = LEdge.UNDIRECTED;
            grMngr.highlightElement(g, null, null, true, (wheelDirection  == ViewListener.WHEEL_UP)?-1:1, false, dir); // g is guaranteed to be != null, don't care about camera and cursor
        }
        else if (inZoomWindow){
            tfactor = (grMngr.dmCamera.focal+Math.abs(grMngr.dmCamera.altitude))/grMngr.dmCamera.focal;
            if (wheelDirection  == WHEEL_UP){
                // zooming in
                grMngr.dmCamera.altitudeOffset(-tfactor*WHEEL_ZOOMOUT_FACTOR);
            }
            else {
                // wheelDirection == WHEEL_DOWN, zooming out
                grMngr.dmCamera.altitudeOffset(tfactor*WHEEL_ZOOMIN_FACTOR);
            }
            grMngr.updateMagWindow();
            grMngr.vsm.repaint();
        }
        else {
            tfactor = (grMngr.mainCamera.focal+Math.abs(grMngr.mainCamera.altitude))/grMngr.mainCamera.focal;
            mvx = v.getVCursor().getVSXCoordinate();
            mvy = v.getVCursor().getVSYCoordinate();
            if (wheelDirection == WHEEL_UP){
                // zooming out
                grMngr.mainCamera.vx -= Math.round((mvx - grMngr.mainCamera.vx) * WHEEL_ZOOMOUT_FACTOR / grMngr.mainCamera.focal);
                grMngr.mainCamera.vy -= Math.round((mvy - grMngr.mainCamera.vy) * WHEEL_ZOOMOUT_FACTOR / grMngr.mainCamera.focal);
                grMngr.mainCamera.altitudeOffset(tfactor*WHEEL_ZOOMOUT_FACTOR);
                grMngr.cameraMoved(null, null, 0);
            }
            else {
                // wheelDirection == WHEEL_DOWN, zooming in
                if (grMngr.mainCamera.getAltitude() > -90){
                    grMngr.mainCamera.vx += Math.round((mvx - grMngr.mainCamera.vx) * WHEEL_ZOOMIN_FACTOR / grMngr.mainCamera.focal);
                    grMngr.mainCamera.vy += Math.round((mvy - grMngr.mainCamera.vy) * WHEEL_ZOOMIN_FACTOR / grMngr.mainCamera.focal);
                }
                grMngr.mainCamera.altitudeOffset(-tfactor*WHEEL_ZOOMIN_FACTOR);
                grMngr.cameraMoved(null, null, 0);
            }
        }
    }

    public void enterGlyph(Glyph g){
        grMngr.mainView.setStatusBarText(Messages.SPACE_STRING);
        if (g == grMngr.magWindow){
            inMagWindow = true;
            return;
        }
        // do not highlight graph's bounding box
        if (g == grMngr.boundingBox){return;}
        if (grMngr.vsm.getActiveView().getActiveLayer() == 1){
            // interacting with pie menu
            g.highlight(true, null);
            VirtualSpace vs = grMngr.vsm.getVirtualSpace(grMngr.menuSpace);
            vs.onTop(g);
            int i = fr.inria.zvtm.engine.Utils.indexOfGlyph(application.mainPieMenu.getItems(), g);
            if (i != -1){
                vs.onTop(application.mainPieMenu.getLabels()[i]);
            }
            else {
                i = fr.inria.zvtm.engine.Utils.indexOfGlyph(application.subPieMenu.getItems(), g);
                if (i != -1){
                    vs.onTop(application.subPieMenu.getLabels()[i]);
                }
            }
        }
        else {
            if (g.getType() != null){
                if (g.getType().equals(GeometryEditor.SPLINE_GEOM_EDITOR)){
                    grMngr.mainView.setCursorIcon(Cursor.MOVE_CURSOR);
                }
                else if (g.getType().equals(ToolPalette.TOOLPALETTE_BUTTON)){
                    g.highlight(true, null);
                }
            }
            else if (grMngr.tp.isHighlightMode()){
                // node & neighbors highlighting in higlight mode
                // g is guaranteed to be != null, don't care about camera and cursor
                grMngr.highlightElement(g, null, null, true, 0, false, -1);
            }
            else {
                // regular node highlighting
                g.highlight(true, null);
            }

        }
    }

    public void exitGlyph(Glyph g){
        if (g == grMngr.magWindow){
            inMagWindow = false;
            return;
        }
        // do not highlight graph's bounding box
        if (g == grMngr.boundingBox){return;}
        if (grMngr.vsm.getActiveView().getActiveLayer() == 1){
            g.highlight(false, null);
            if (application.mainPieMenu != null && g == application.mainPieMenu.getBoundary()){
                Glyph lge = grMngr.vsm.getActiveView().mouse.getPicker().lastGlyphEntered();
                if (lge != null && lge.getType() == Messages.PM_SUBMN){
                    application.mainPieMenu.setSensitivity(false);
                    application.displaySubMenu(lge, true);
                }
            }
            else if (application.subPieMenu != null && g == application.subPieMenu.getBoundary()){
                application.displaySubMenu(null, false);
                application.mainPieMenu.setSensitivity(true);
            }
        }
        else {
            if (g.getType() != null){
                if (g.getType().equals(GeometryEditor.SPLINE_GEOM_EDITOR)){
                    grMngr.mainView.setCursorIcon(Cursor.CUSTOM_CURSOR);
                }
                else if (g.getType().equals(ToolPalette.TOOLPALETTE_BUTTON)){
                    g.highlight(false, null);
                }
            }
            else if (application.grMngr.tp.isHighlightMode()){
                // node & neighbors highlighting in higlight mode
                grMngr.unhighlightAll();
            }
            else {
                // regular node highlighting
                g.highlight(false, null);
            }
        }
    }

    public void Ktype(ViewPanel v,char c,int code,int mod, KeyEvent e){}

    public void Kpress(ViewPanel v,char c,int code,int mod, KeyEvent e){
        if(code==KeyEvent.VK_PAGE_UP){grMngr.getHigherView();}
        else if (code==KeyEvent.VK_PAGE_DOWN){grMngr.getLowerView();}
        else if (code==KeyEvent.VK_HOME){grMngr.getGlobalView();}
        else if (code==KeyEvent.VK_UP){grMngr.translateView(GraphicsManager.MOVE_DOWN);}
        else if (code==KeyEvent.VK_DOWN){grMngr.translateView(GraphicsManager.MOVE_UP);}
        else if (code==KeyEvent.VK_LEFT){grMngr.translateView(GraphicsManager.MOVE_RIGHT);}
        else if (code==KeyEvent.VK_RIGHT){grMngr.translateView(GraphicsManager.MOVE_LEFT);}
        else if (code==KeyEvent.VK_L || code==KeyEvent.VK_SPACE){
            Glyph g=v.lastGlyphEntered();
            if (g!=null){
                if (g.getOwner()!=null){getAndDisplayURL((LElem)g.getOwner(), g);}
            }
            else {
                attemptDisplayEdgeURL(v.getVCursor(),v.cams[0]);
            }
        }
    }

    public void Krelease(ViewPanel v,char c,int code,int mod, KeyEvent e){}

    public void viewActivated(View v){}

    public void viewDeactivated(View v){}

    public void viewIconified(View v){}

    public void viewDeiconified(View v){}

    public void viewClosing(View v){application.exit();}

    public void attemptDisplayEdgeURL(VCursor mouse,Camera cam){
        Glyph g;
        Vector otherGlyphs = mouse.getPicker().getIntersectingGlyphs(cam);
        if (otherGlyphs!=null && otherGlyphs.size()>0){
            g = (Glyph)otherGlyphs.firstElement();
            if (g.getOwner()!=null){getAndDisplayURL((LElem)g.getOwner(), g);}
        }
    }

    public void getAndDisplayURL(LElem noa, Glyph g){
        String url = noa.getURL(g);
        if (url!=null && url.length()>0){
            application.displayURLinBrowser(url);
        }
    }

}
