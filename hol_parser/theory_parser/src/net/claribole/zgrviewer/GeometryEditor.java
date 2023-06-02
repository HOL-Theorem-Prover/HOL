/*   Copyright (c) INRIA, 2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: GeometryEditor.java 4822 2012-03-15 14:38:36Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Color;
import java.awt.geom.Point2D;

import fr.inria.zvtm.engine.VirtualSpaceManager;
import fr.inria.zvtm.glyphs.SICircle;
import fr.inria.zvtm.glyphs.VSegment;
import fr.inria.zvtm.glyphs.VPolygon;
import fr.inria.zvtm.glyphs.VPolygonOr;
import fr.inria.zvtm.glyphs.DPath;
import fr.inria.zvtm.glyphs.ClosedShape;
import fr.inria.zvtm.glyphs.Glyph;

public class GeometryEditor {

    public static final String SPLINE_GEOM_EDITOR = "sge";

    GraphicsManager grMngr;
    Point2D.Double[] currentEditPoints;
    SICircle[] currentEditPointGlyphs;
    VSegment[] currentEditSegments;
    DPath currentEditSpline;

    GeometryEditor(GraphicsManager gm){
        this.grMngr = gm;
    }

    /*-------------------- Editing edges -----------------*/

    double headTangent, tailTangent = 0;
    double headOrient, tailOrient = 0;

    void editEdgeSpline(LEdge e){
        currentEditSpline = e.getSpline();
        currentEditPoints = currentEditSpline.getAllPointsCoordinates();
        // take care of head glyph
        Glyph head = e.getHeadGlyph();
        headTangent = Math.atan2(currentEditPoints[currentEditPoints.length-1].y-currentEditPoints[currentEditPoints.length-2].y,
                                 currentEditPoints[currentEditPoints.length-1].x-currentEditPoints[currentEditPoints.length-2].x);
        if (head != null){
            if ((head instanceof VPolygon) && !(head instanceof VPolygonOr)){
                VPolygon p = (VPolygon)head;
                VPolygonOr newHead = new VPolygonOr(p.getAbsoluteVertices(), 0, p.getDefaultColor(), p.getDefaultBorderColor(), 0);
                newHead.moveTo(currentEditPoints[currentEditPoints.length-1].x, currentEditPoints[currentEditPoints.length-1].y);
                e.replaceHead(newHead);
                newHead.setType(head.getType());
                grMngr.mSpace.removeGlyph(head, false);
                grMngr.mSpace.addGlyph(newHead, false);
                head = newHead;
            }
            // else consider that the glyph is already reorientable (should work in most - if not all - cases)
            headOrient = head.getOrient();
        }
        // take care of tail glyph
        Glyph tail = e.getTailGlyph();
        tailTangent = Math.atan2(currentEditPoints[0].y-currentEditPoints[1].y,
                                 currentEditPoints[0].x-currentEditPoints[1].x);
        if (tail != null){
            if ((tail instanceof VPolygon) && !(tail instanceof VPolygonOr)){
                VPolygonOr newTail = new VPolygonOr(((VPolygon)tail).getAbsoluteVertices(), 0, tail.getColor(), tail.getBorderColor(), 0);
                newTail.moveTo(currentEditPoints[0].x, currentEditPoints[0].y);
                e.replaceTail(newTail);
                newTail.setType(tail.getType());
                grMngr.mSpace.removeGlyph(tail, false);
                grMngr.mSpace.addGlyph(newTail, false);
                tail = newTail;
            }
            // else consider that the glyph is already reorientable (should work in most - if not all - cases)
            tailOrient = tail.getOrient();
        }
        if (tail != null || head != null){
            for (Glyph g:e.getUnknownGlyphs()){
                if (g instanceof VSegment){grMngr.mSpace.removeGlyph(g, false);}
            }
        }
        // show glyphs for editing control points
        currentEditPointGlyphs = new SICircle[currentEditPoints.length];
        currentEditSegments = new VSegment[currentEditPointGlyphs.length-1];
        currentEditPointGlyphs[0] = new SICircle(currentEditPoints[0].x, currentEditPoints[0].y, 100, 6, Color.DARK_GRAY, Color.LIGHT_GRAY, .8f);
        currentEditPointGlyphs[0].setType(SPLINE_GEOM_EDITOR);
        for (int i=1;i<currentEditPoints.length;i++){
            currentEditPointGlyphs[i] = new SICircle(currentEditPoints[i].x, currentEditPoints[i].y, 100, 6, Color.DARK_GRAY, Color.LIGHT_GRAY, .8f);
            currentEditPointGlyphs[i].setType(SPLINE_GEOM_EDITOR);
            currentEditSegments[i-1] = new VSegment(currentEditPoints[i-1].x, currentEditPoints[i-1].y, currentEditPoints[i].x, currentEditPoints[i].y, 99, Color.RED, .6f);
        }
        grMngr.mSpace.addGlyphs(currentEditSegments, false);
        grMngr.mSpace.addGlyphs(currentEditPointGlyphs, true);
    }

    void updateEdgeSpline(){
        for (int i=0;i<currentEditSegments.length;i++){
            currentEditSegments[i].setEndPoints(currentEditPointGlyphs[i].vx, currentEditPointGlyphs[i].vy,
                                                currentEditPointGlyphs[i+1].vx, currentEditPointGlyphs[i+1].vy);
        }
        for (int i=0;i<currentEditPointGlyphs.length;i++){
            currentEditPoints[i].setLocation(currentEditPointGlyphs[i].vx, currentEditPointGlyphs[i].vy);
        }
        currentEditSpline.edit(currentEditPoints, true);
        ClosedShape head = ((LEdge)currentEditSpline.getOwner()).getHeadGlyph();
        if (head != null){
            double newHeadTangent = Math.atan2(currentEditPoints[currentEditPoints.length-1].y-currentEditPoints[currentEditPoints.length-2].y,
                                              currentEditPoints[currentEditPoints.length-1].x-currentEditPoints[currentEditPoints.length-2].x);
            head.orientTo(headOrient+(newHeadTangent-headTangent));
            head.moveTo(currentEditPoints[currentEditPoints.length-1].x, currentEditPoints[currentEditPoints.length-1].y);
        }
        ClosedShape tail = ((LEdge)currentEditSpline.getOwner()).getTailGlyph();
        if (tail != null){
            double newTailTangent = Math.atan2(currentEditPoints[0].y-currentEditPoints[1].y,
                                               currentEditPoints[0].x-currentEditPoints[1].x);
            tail.orientTo(tailOrient+(newTailTangent-tailTangent));
            tail.moveTo(currentEditPoints[0].x, currentEditPoints[0].y);
        }
    }

    void clearSplineEditingGlyphs(){
        if (currentEditPoints != null){
            for (VSegment s:currentEditSegments){
                grMngr.mSpace.removeGlyph(s, false);
            }
            for (SICircle c:currentEditPointGlyphs){
                grMngr.mSpace.removeGlyph(c, false);
            }
            VirtualSpaceManager.INSTANCE.repaint();
        }
        currentEditSpline = null;
        currentEditPointGlyphs = null;
        currentEditSegments = null;
        currentEditPoints = null;
    }

    /*-------------------- Moving nodes -----------------*/

    Glyph manipulatedNodeGlyph;

    void stickNodeComponents(Glyph mg, LNode n){
        manipulatedNodeGlyph = mg;
        for (Glyph g:n.getGlyphs()){
            if (g != manipulatedNodeGlyph){
                manipulatedNodeGlyph.stick(g);
            }
        }
    }

    void unstickAll(){
        manipulatedNodeGlyph.unstickAllGlyphs();
        manipulatedNodeGlyph = null;
    }

}
