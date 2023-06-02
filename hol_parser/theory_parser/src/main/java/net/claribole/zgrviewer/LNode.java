/*   FILE: LNode.java
 *   DATE OF CREATION:  Thu Mar 15 19:18:17 2007
 *   Copyright (c) INRIA, 2007-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: LNode.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.util.Vector;

import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.glyphs.ClosedShape;
import fr.inria.zvtm.glyphs.VText;
import fr.inria.zvtm.svg.Metadata;

public class LNode extends LElem {

    LEdge[] edges;
    short[] edgeDirections;

    LNode(String title, Vector<Glyph> gls){
        this.title = title;
        this.glyphs = new Glyph[gls.size()];
        this.URLs = new String[gls.size()];
        this.tooltips = new String[gls.size()];
        for (int i=0;i<this.glyphs.length;i++){
            this.glyphs[i] = gls.elementAt(i);
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
        edges = new LEdge[0];
        edgeDirections = new short[0];
    }

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

    void addArc(LEdge e, short direction){
        LEdge[] nedges = new LEdge[edges.length+1];
        short[] nedgeDirections = new short[edgeDirections.length+1];
        System.arraycopy(edges, 0, nedges, 0, edges.length);
        System.arraycopy(edgeDirections, 0, nedgeDirections, 0, edgeDirections.length);
        nedges[edges.length] = e;
        nedgeDirections[edgeDirections.length] = direction;
        edges = nedges;
        edgeDirections = nedgeDirections;
    }

    void removeArc(LEdge e){
        int index = -1;
        // find edge index in array
        for (int i=0;i<edges.length;i++){
            if (edges[i] == e){index = i;break;}
        }
        if (index != -1){
            // then remove it (if found)
            LEdge[] nedges = new LEdge[edges.length-1];
            short[] nedgeDirections = new short[edgeDirections.length-1];
            System.arraycopy(edges, 0, nedges, 0, index);
            System.arraycopy(edges, index+1, nedges, index, edges.length-index-1);
            System.arraycopy(edgeDirections, 0, nedgeDirections, 0, index);
            System.arraycopy(edgeDirections, index+1, nedgeDirections, index, edgeDirections.length-index-1);
            edges = nedges;
            edgeDirections = nedgeDirections;
        }
    }

    public LEdge[] getAllArcs(){
        LEdge[] res = new LEdge[edges.length];
        System.arraycopy(edges, 0, res, 0, edges.length);
        return res;
    }

    /** Get all arcs incoming or outgoing from this node, except for the specified one. */
    public LEdge[] getOtherArcs(LEdge arc){
        int count = 0;
        for (int i=0;i<edges.length;i++){
            if (arc != edges[i]){count++;}
        }
        LEdge[] res = new LEdge[count];
        int j = 0;
        for (int i=0;i<edges.length;i++){
            if (arc != edges[i]){res[j++] = edges[i];}
        }
        return res;
    }

    public LEdge[] getOutgoingArcs(){
        int oaCount = 0;
        for (int i=0;i<edgeDirections.length;i++){
            if (edgeDirections[i] == LEdge.OUTGOING){oaCount++;}
        }
        LEdge[] res = new LEdge[oaCount];
        int j = 0;
        for (int i=0;i<edges.length;i++){
            if (edgeDirections[i] == LEdge.OUTGOING){
                res[j++] = edges[i];
            }
        }
        return res;
    }

    public LEdge[] getIncomingArcs(){
        int oaCount = 0;
        for (int i=0;i<edgeDirections.length;i++){
            if (edgeDirections[i] == LEdge.INCOMING){oaCount++;}
        }
        LEdge[] res = new LEdge[oaCount];
        int j = 0;
        for (int i=0;i<edges.length;i++){
            if (edgeDirections[i] == LEdge.INCOMING){
                res[j++] = edges[i];
            }
        }
        return res;
    }

    public LEdge[] getUndirectedArcs(){
        int oaCount = 0;
        for (int i=0;i<edgeDirections.length;i++){
            if (edgeDirections[i] == LEdge.UNDIRECTED){oaCount++;}
        }
        LEdge[] res = new LEdge[oaCount];
        int j = 0;
        for (int i=0;i<edges.length;i++){
            if (edgeDirections[i] == LEdge.UNDIRECTED){
                res[j++] = edges[i];
            }
        }
        return res;
    }

    public ClosedShape getShape(){
        for (int i=0;i<glyphs.length;i++){
            if (glyphs[i] instanceof ClosedShape){return (ClosedShape)glyphs[i];}
        }
        return null;
    }

    public VText getLabel(){
        for (int i=0;i<glyphs.length;i++){
            if (glyphs[i] instanceof VText){return (VText)glyphs[i];}
        }
        return null;
    }

    public String toString(){
        String res = title + "[";
        for (int i=0;i<edges.length;i++){
            res += ((edges[i] != null) ? edges[i].title + "@" + edges[i].hashCode() : "NULL") + "(" + edgeDirections[i] + ") ";
        }
        res += "]";
        return res;
    }

}
