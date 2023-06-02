/*   Copyright (c) INRIA, 2012. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: LGraph.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Color;
import java.awt.geom.Point2D;
import java.util.Vector;

import fr.inria.zvtm.engine.VirtualSpace;
import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.glyphs.ClosedShape;
import fr.inria.zvtm.glyphs.DPath;
import fr.inria.zvtm.glyphs.VRectangle;
import fr.inria.zvtm.glyphs.VRoundRect;
import fr.inria.zvtm.glyphs.VSegment;
import fr.inria.zvtm.glyphs.VText;
import fr.inria.zvtm.svg.Metadata;

public class LGraph extends LElem {

    public static final short BOX_TYPE_NONE = 0;
    public static final short BOX_TYPE_RECT = 1;
    public static final short BOX_TYPE_ROUND_RECT = 2;

    Vector<LNode> nodes = new Vector(1);
    Vector<LGraph> subgraphs = new Vector(1);

    LGraph(String title, Vector<Glyph> gls, VirtualSpace mSpace){
        this.title = title;
        VRoundRect aRoundedBoxIndeed = null;
        if (gls.size() == 8 && (gls.firstElement() instanceof VSegment || gls.firstElement() instanceof DPath)){
            // likely to be a rounded box
            aRoundedBoxIndeed = attemptRoundedBoxReconstruction(gls);
            this.glyphs = new Glyph[]{aRoundedBoxIndeed};
            mSpace.addGlyph(aRoundedBoxIndeed);
            mSpace.above(aRoundedBoxIndeed, gls.lastElement());
            aRoundedBoxIndeed.setOwner(this);
            for (Glyph g:gls){
                mSpace.removeGlyph(g);
            }
        }
        if (aRoundedBoxIndeed == null){
            // if it is not a rounded box, then store the glyphs as is
            // - a regular box will be stored as a single VRectangle
            // - other glyphs, likely not boxes, will be stored the way they were declared in the SVG
            this.glyphs = new Glyph[gls.size()];
            for (int i=0;i<this.glyphs.length;i++){
                this.glyphs[i] = gls.elementAt(i);
                this.glyphs[i].setOwner(this);
            }
        }
    }

    VRoundRect attemptRoundedBoxReconstruction(Vector<Glyph> gls){
        Vector<VSegment> sides = new Vector(4);
        Vector<Glyph> corners = new Vector(4);
        for (Glyph gl:gls){
            if (gl instanceof DPath){corners.add(gl);}
            else if (gl instanceof VSegment){sides.add((VSegment)gl);}
            // else do nothing
        }
        if (sides.size() == 4 && corners.size() == 4){
            try {
                // likely to be a rounded box
                VSegment westSide = sides.firstElement();
                VSegment eastSide = sides.firstElement();
                VSegment northSide = sides.firstElement();
                VSegment southSide = sides.firstElement();
                for (int i=1;i<sides.size();i++){
                    VSegment candidateSide = sides.elementAt(i);
                    if (candidateSide.vx < westSide.vx){westSide = candidateSide;}
                    if (candidateSide.vx > eastSide.vx){eastSide = candidateSide;}
                    if (candidateSide.vy > northSide.vy){northSide = candidateSide;}
                    if (candidateSide.vy < southSide.vy){southSide = candidateSide;}
                }
                // compute corner radius
                Point2D.Double[] nsep = northSide.getEndPoints();
                double cornerRadius = 2 * (eastSide.vx - Math.max(nsep[0].x, nsep[1].x));
                // instantiate corresponding VRoundRect
                VRoundRect ng = new VRoundRect((westSide.vx+eastSide.vx)/2.0, (northSide.vy+southSide.vy)/2.0, 0,
                                               eastSide.vx-westSide.vx, northSide.vy-southSide.vy,
                                               Color.WHITE, westSide.getColor(), 1f, cornerRadius, cornerRadius);
                ng.setFilled(false);
                ng.setStroke(westSide.getStroke());
                return ng;
            }
            catch (Exception ex){
                System.err.println("ZGRViewer: WARNING: attempt at constructing rounded subgraph box failed for " + this.title);
                return null;
            }
        }
        else {
            // not a rounded box
            return null;
        }
    }

    /** Get the type of box used to paint the boundaries of this subgraph.
     *@see #getGlyphs()
     *@return one of BOX_TYPE_*
     */
    public short getBoxType(){
        for (Glyph g:glyphs){
            if (g instanceof VRoundRect){return BOX_TYPE_ROUND_RECT;}
            else if (g instanceof VRectangle){return BOX_TYPE_RECT;}
            // else keep looking for one
        }
        return BOX_TYPE_NONE;
    }

    /** Get all glyphs representing this subgraph.
     * This can include the boundary box (a VRectangle or VRoundRect), some VText (subgraph title).
     *@see #getBoxType()
     */
    public Glyph[] getGlyphs(){
        return glyphs;
    }

    public ClosedShape getBox(){
        ClosedShape res = null;
        for (Glyph g:glyphs){
            if (g instanceof ClosedShape){
                if (res == null || g.getSize() > res.getSize()){
                    res = (ClosedShape)g;
                }
            }
        }
        return res;
    }

    public VText[] getLabels(){
        Vector<VText> labels = new Vector(2);
        for (Glyph g:glyphs){
            if (g instanceof VText){
                labels.add((VText)g);
            }
        }
        return labels.toArray(new VText[labels.size()]);
    }

    public void addChildNode(LNode n){
        if (!nodes.contains(n)){
            nodes.add(n);
        }
    }

    public LNode[] getChildNodes(){
        return nodes.toArray(new LNode[nodes.size()]);
    }

    public String toString(){
        String res = "subgraph "+title + " - subgraphs[";
        for (LGraph subgraph:subgraphs){
            res += subgraph.getTitle() + ", ";
        }
        res += "] - nodes[";
        for (LNode node:nodes){
            res += node.getTitle() + ", ";
        }
        res += "]";
        return res;
    }

    public void addSubgraph(LGraph g){
        if (!subgraphs.contains(g)){
            subgraphs.add(g);
        }
    }

    public LGraph[] getSubgraphs(){
        return subgraphs.toArray(new LGraph[subgraphs.size()]);
    }

}
