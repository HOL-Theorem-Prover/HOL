/*   FILE: LEdge.java
 *   DATE OF CREATION:  Thu Mar 15 19:18:17 2007
 *   Copyright (c) INRIA, 2007-2013. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: LEdge.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.geom.Point2D;

import java.util.Vector;

import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.glyphs.DPath;
import fr.inria.zvtm.glyphs.VPolygon;
import fr.inria.zvtm.glyphs.VPolygonOr;
import fr.inria.zvtm.glyphs.VText;
import fr.inria.zvtm.glyphs.ClosedShape;
import fr.inria.zvtm.svg.Metadata;

public class LEdge extends LElem {

    static final short UNDIRECTED = 0;
    static final short INCOMING = 1;
    static final short OUTGOING = 2;

    static final String UNDIRECTED_STR = "--";
    static final String DIRECTED_STR = "->";

    static final short GLYPH_SPLINE = 0;
    static final short GLYPH_LABEL = 1;
    static final short GLYPH_HEAD = 2;
    static final short GLYPH_TAIL = 3;
    static final short GLYPH_UNKNOWN = 4;

    short[] glyphCat;

    boolean directed = false;

    LNode tail;
    LNode head;

    LEdge(String title, Vector<Glyph> glyphs){
        this.title = title;
        this.glyphs = new Glyph[glyphs.size()];
        this.URLs = new String[glyphs.size()];
        this.tooltips = new String[glyphs.size()];
        for (int i=0;i<this.glyphs.length;i++){
            this.glyphs[i] = glyphs.elementAt(i);
            // URL associated with each glyph (there might be different URLs associated with
            // the various glyphs constituting a node or edge)
            if (this.glyphs[i].getOwner() != null){
                URLs[i] = ((Metadata)this.glyphs[i].getOwner()).getURL();
                tooltips[i] = ((Metadata)this.glyphs[i].getOwner()).getURLTitle();
            }
        }
        if (this.glyphs.length > 0){
            this.groupID = ((Metadata)this.glyphs[0].getOwner()).getClosestAncestorGroupID();
        }
        else {
            this.groupID = Messages.EMPTY_STRING;
        }
        for (int i=0;i<this.glyphs.length;i++){
            this.glyphs[i].setOwner(this);
        }
        categorizeGlyphs();
    }

    LEdge(Vector<Glyph> glyphs){
        this.title = "";
        this.glyphs = new Glyph[glyphs.size()];
        this.URLs = new String[glyphs.size()];
        this.tooltips = new String[glyphs.size()];
        for (int i=0;i<this.glyphs.length;i++){
            this.glyphs[i] = glyphs.elementAt(i);
            this.glyphs[i].setOwner(this);
            this.URLs[i] = "";
            this.tooltips[i] = "";
        }
        this.groupID = Messages.EMPTY_STRING;
        categorizeGlyphs();
    }

    void categorizeGlyphs(){
        glyphCat = new short[glyphs.length];
        Point2D.Double sp = getSpline().getStartPoint();
        Point2D.Double ep = getSpline().getEndPoint();
        for (int i=0;i<glyphs.length;i++){
            if (glyphs[i] instanceof DPath){
                // the spline itself
                glyphCat[i] = GLYPH_SPLINE;
            }
            else if (glyphs[i] instanceof VText){
                // probably a label
                glyphCat[i] = GLYPH_LABEL;
            }
            else if (glyphs[i] instanceof ClosedShape){
                if (Math.sqrt((glyphs[i].vx-sp.x)*(glyphs[i].vx-sp.x) + (glyphs[i].vy-sp.y)*(glyphs[i].vy-sp.y))
                    < Math.sqrt((glyphs[i].vx-ep.x)*(glyphs[i].vx-ep.x) + (glyphs[i].vy-ep.y)*(glyphs[i].vy-ep.y))){
                    // probably a tail glyph
                    glyphCat[i] = GLYPH_TAIL;
                }
                else {
                    // probably a head glyph
                    glyphCat[i] = GLYPH_HEAD;
                }
            }
            else {
                glyphCat[i] = GLYPH_UNKNOWN;
            }
        }
    }

    //void printCats(){
    //    for (int i=0;i<glyphs.length;i++){
    //        System.out.println(glyphs[i]+"\t=\t"+glyphCat[i]);
    //    }
    //    System.out.println();
    //}

    public String getURL(Glyph g){
        for (int i=0;i<glyphs.length;i++){
            if (g == glyphs[i]){
                return URLs[i];
            }
        }
        return null;
    }

    public String getTooltip(Glyph g){
        for (int i=0;i<glyphs.length;i++){
            if (g == glyphs[i]){
                return tooltips[i];
            }
        }
        return null;
    }

    void setDirected(boolean b){
    directed = b;
    }

    boolean isDirected(){
    return directed;
    }

    public boolean isLoop(){
        return tail == head;
    }

    void setTail(LNode n){
    tail = n;
    if (tail != null){
        tail.addArc(this, (directed) ? LEdge.OUTGOING : LEdge.UNDIRECTED);
    }
    }

    void setHead(LNode n){
    head = n;
    if (head != null){
        head.addArc(this, (directed) ? LEdge.INCOMING : LEdge.UNDIRECTED);
    }
    }

    public LNode getTail(){
        return tail;
    }

    public LNode getHead(){
        return head;
    }

    public LNode getOtherEnd(LNode n){
        return (n == tail) ? head : tail;
    }

    public DPath getSpline(){
        for (int i=0;i<glyphs.length;i++){
            if (glyphCat[i] == GLYPH_SPLINE){return (DPath)glyphs[i];}
        }
        return null;
    }

    /**
     *@return null if none or could not be identified.
     *@see #getTailGlyph()
     */
    public ClosedShape getHeadGlyph(){
        for (int i=0;i<glyphs.length;i++){
            if (glyphCat[i] == GLYPH_HEAD){return (ClosedShape)glyphs[i];}
        }
        return null;
    }

    /**
     *@return null if none or could not be identified.
     *@see #getHeadGlyph()
     */
    public ClosedShape getTailGlyph(){
        for (int i=0;i<glyphs.length;i++){
            if (glyphCat[i] == GLYPH_TAIL){return (ClosedShape)glyphs[i];}
        }
        return null;
    }

    public Glyph[] getUnknownGlyphs(){
        Vector<Glyph> res = new Vector(1);
        for (int i=0;i<glyphs.length;i++){
            if (glyphCat[i] == GLYPH_UNKNOWN){
                res.add(glyphs[i]);
            }
        }
        return res.toArray(new Glyph[res.size()]);
    }

    public boolean hasTailAndHeadGlyphs(){
        int countH = 0;
        int countT = 0;
        for (int i=0;i<glyphs.length;i++){
            if (glyphCat[i] == GLYPH_HEAD){countH++;}
            else if (glyphCat[i] == GLYPH_TAIL){countT++;}
        }
        return (countH > 0 && countT > 0);
    }

    /**
     *@return the old polygon if replace was successful.
     */
    public ClosedShape replaceHead(VPolygonOr s){
        for (int i=0;i<glyphs.length;i++){
            if (glyphCat[i] == GLYPH_HEAD){
                ClosedShape old = (ClosedShape)glyphs[i];
                glyphs[i] = s;
                s.setOwner(this);
                return old;
            }
        }
        return null;
    }

    /**
     *@return the old polygon if replace was successful.
     */
    public ClosedShape replaceTail(VPolygonOr s){
        for (int i=0;i<glyphs.length;i++){
            if (glyphCat[i] == GLYPH_TAIL){
                ClosedShape old = (ClosedShape)glyphs[i];
                glyphs[i] = s;
                s.setOwner(this);
                return old;
            }
        }
        return null;
    }

    public String toString(){
    return title + "@" + hashCode() + " [" +
        ((tail != null) ? tail.getTitle() + "@" + tail.hashCode() : "NULL")+
        ((directed) ? LEdge.DIRECTED_STR : LEdge.UNDIRECTED_STR) +
        ((head != null) ? head.getTitle() + "@" + head.hashCode() : "NULL") +
        "]";
    }

}
