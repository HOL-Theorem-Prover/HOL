/*   FILE: LogicalStructure.java
 *   DATE OF CREATION:  Thu Mar 15 18:33:17 2007
 *   Copyright (c) INRIA, 2007-2012. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: LogicalStructure.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.HashMap;
import java.util.Vector;

import fr.inria.zvtm.engine.VirtualSpace;
import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.glyphs.RectangularShape;
import fr.inria.zvtm.svg.Metadata;

public class LogicalStructure {

    static final String GRAPH_PREFIX = "graph";
    static final String NODE_PREFIX = "node";
    static final String EDGE_PREFIX = "edge";

    public static LogicalStructure build(Vector glyphs, VirtualSpace mSpace){
        Glyph g;
        Metadata md;
        // key = node title, value = vector of glyphs associated with this node
        Hashtable title2node = new Hashtable();
        // key = edge title, value = hashtable in which:
        //           key = closest ancestor group ID,
        //           value = vector of glyphs associated with the
        //                   edge whose id is key
        // this is necessary to avoid all glyphs of different edges linking the same nodes being associated with the same single LEdge
        Hashtable title2edgeGroup = new Hashtable();
        // key = graph title, value = vector of glyphs associated with this subgraph
        Hashtable title2graph = new Hashtable();
        String title;
        Vector v;
        Hashtable t;
        String cagid, cgac;
        int edgeCount = 0;
        for (int i=0;i<glyphs.size();i++){
            g = (Glyph)glyphs.elementAt(i);
            md = (Metadata)g.getOwner();
            if (md != null && (title=md.getTitle()) != null){
                cagid = md.getClosestAncestorGroupID();
                cgac = md.getClosestAncestorGroupClass();
                if (cgac.equals(EDGE_PREFIX) || cagid.startsWith(EDGE_PREFIX)){
                    // dealing with a glyph that is part of an edge
                    if (title2edgeGroup.containsKey(title)){
                        t = (Hashtable)title2edgeGroup.get(title);
                        if (t.containsKey(cagid)){
                            v = (Vector)t.get(cagid);
                            v.add(g);
                        }
                        else {
                            v = new Vector();
                            v.add(g);
                            t.put(cagid, v);
                            edgeCount++;
                        }
                    }
                    else {
                        v = new Vector();
                        v.add(g);
                        // initial capacity set to 3 (path, arrow head, label)
                        t = new Hashtable(3);
                        t.put(cagid, v);
                        title2edgeGroup.put(title, t);
                        edgeCount++;
                    }
                }
                else if (cgac.equals(NODE_PREFIX) || cagid.startsWith(NODE_PREFIX)){
                    // dealing with a glyph that is part of a node
                    if (title2node.containsKey(title)){
                        v = (Vector)title2node.get(title);
                        v.add(g);
                    }
                    else {
                        v = new Vector();
                        v.add(g);
                        title2node.put(title, v);
                    }
                }
                else if (cagid.startsWith(GRAPH_PREFIX) || cgac.equals(GRAPH_PREFIX)){
                    if (title2graph.containsKey(title)){
                        v = (Vector)title2graph.get(title);
                        v.add(g);
                    }
                    else {
                        v = new Vector();
                        v.add(g);
                        title2graph.put(title, v);
                    }
                }
                // else, other stuff that is probably not part of the graph structure, like a graph's background
                // do nothing
            }
            // remain silent if structural information could not be extracted
        }
        LogicalStructure res = new LogicalStructure(title2node, title2edgeGroup, edgeCount, title2graph, mSpace);
        title2edgeGroup.clear();
        title2node.clear();
        title2graph.clear();
        return (res.isEmpty()) ? null : res;
    }

    /* ----------------------------------- */

    LGraph[] graphs;
    LNode[] nodes;
    LEdge[] edges;

    LogicalStructure(Hashtable title2node, Hashtable title2edgeGroup, int edgeCount, Hashtable title2graph, VirtualSpace mSpace){
        String title;
        // construct nodes
        nodes= new LNode[title2node.size()];
        int i = 0;
        for (Enumeration e=title2node.keys();e.hasMoreElements();){
            title = (String)e.nextElement();
            nodes[i] = new LNode(title, (Vector)title2node.get(title));
            i++;
        }
        // construct edges
        i = 0;
        edges = new LEdge[edgeCount];
        Hashtable group2edge;
        for (Enumeration e=title2edgeGroup.keys();e.hasMoreElements();){
            title = (String)e.nextElement();
            group2edge = (Hashtable)title2edgeGroup.get(title);
            for (Enumeration e2=group2edge.elements();e2.hasMoreElements();){
                // we do not save the group/edge's ID, not relevant for now
                // but we could if it prove to be useful (group ID is just the key)
                // and could be given to the LEdge constructor
                edges[i] = new LEdge(title, (Vector)e2.nextElement());
                i++;
            }
        }
        // link nodes and edges
        for (int j=0;j<edges.length;j++){
            int id = edges[j].title.indexOf(LEdge.DIRECTED_STR);
            if (id != -1){
                edges[j].setDirected(true);
                edges[j].setTail(getNode(edges[j].title.substring(0, id)));
                edges[j].setHead(getNode(edges[j].title.substring(id+2)));
            }
            else {
                id = edges[j].title.indexOf(LEdge.UNDIRECTED_STR);
                if (id != -1){
                    edges[j].setDirected(false);
                    edges[j].setTail(getNode(edges[j].title.substring(0, id)));
                    edges[j].setHead(getNode(edges[j].title.substring(id+2)));
                }
            }
        }
        // construct subgraphs
        graphs = new LGraph[title2graph.size()];
        i = 0;
        for (Enumeration e=title2graph.keys();e.hasMoreElements();){
            title = (String)e.nextElement();
            graphs[i] = new LGraph(title, (Vector)title2graph.get(title), mSpace);
            i++;
        }
        // assign LNodes to LGraphs
        for (LGraph graph:graphs){
            Glyph graphBox_g = null;
            RectangularShape graphBox_rs = null;
            if (graph.getBoxType() != LGraph.BOX_TYPE_NONE){
                graphBox_g = graph.getBox();
                graphBox_rs = (RectangularShape)graphBox_g;
            }
            if (graphBox_g == null){continue;}
            for (LNode node:nodes){
                Glyph nodeShape = node.getShape();
                // original test:
                // nodeShape.vx > (graphBox_g.vx-graphBox_rs.getWidth()/2d)
                // && nodeShape.vx < (graphBox_g.vx+graphBox_rs.getWidth()/2d)
                // && nodeShape.vy > (graphBox_g.vy-graphBox_rs.getHeight()/2d)
                // && nodeShape.vy < (graphBox_g.vy+graphBox_rs.getHeight()/2d)
                // optimised as:
                if (nodeShape.vx < (graphBox_g.vx-graphBox_rs.getWidth()/2d)
                    || nodeShape.vx > (graphBox_g.vx+graphBox_rs.getWidth()/2d)
                    || nodeShape.vy < (graphBox_g.vy-graphBox_rs.getHeight()/2d)
                    || nodeShape.vy > (graphBox_g.vy+graphBox_rs.getHeight()/2d)){
                    continue;
                }
                graph.addChildNode(node);
            }
        }
        // assign LGraphs to LGraphs (subgraph relationships)
        for (LGraph graphA:graphs){
            if (graphA.getBoxType() == LGraph.BOX_TYPE_NONE){continue;}
            Glyph graphABox_g = graphA.getBox();
            RectangularShape graphABox_rs = (RectangularShape)graphABox_g;
            for (LGraph graphB:graphs){
                if (graphA != graphB && graphB.getBoxType() != LGraph.BOX_TYPE_NONE){
                    Glyph graphBBox_g = graphB.getBox();
                    RectangularShape graphBBox_rs = (RectangularShape)graphBBox_g;
                    // if graphA's box is fully contained within graphB's box
                    // graphA is a subgraph of graphB
                    // original test:
                    // (graphABox_g.vx-graphABox_rs.getWidth()/2d) > (graphBBox_g.vx-graphBBox_rs.getWidth()/2d)
                    // && (graphABox_g.vx+graphABox_rs.getWidth()/2d) < (graphBBox_g.vx+graphBBox_rs.getWidth()/2d)
                    // && (graphABox_g.vy-graphABox_rs.getHeight()/2d) > (graphBBox_g.vy-graphBBox_rs.getHeight()/2d)
                    // && (graphABox_g.vy+graphABox_rs.getHeight()/2d) < (graphBBox_g.vy+graphBBox_rs.getHeight()/2d)
                    // optimized as:
                    if ((graphABox_g.vx-graphABox_rs.getWidth()/2d) < (graphBBox_g.vx-graphBBox_rs.getWidth()/2d)
                        || (graphABox_g.vx+graphABox_rs.getWidth()/2d) > (graphBBox_g.vx+graphBBox_rs.getWidth()/2d)
                        || (graphABox_g.vy-graphABox_rs.getHeight()/2d) < (graphBBox_g.vy-graphBBox_rs.getHeight()/2d)
                        || (graphABox_g.vy+graphABox_rs.getHeight()/2d) > (graphBBox_g.vy+graphBBox_rs.getHeight()/2d)){
                        continue;
                    }
                    graphB.addSubgraph(graphA);
                }
            }
        }
    }

    public void addEdge(LEdge e){
        LEdge[] nedges = new LEdge[edges.length+1];
        System.arraycopy(edges, 0, nedges, 0, edges.length);
        nedges[edges.length] = e;
        edges = nedges;
    }

    public void removeEdge(LEdge e){
        int index = -1;
        // find edge index in array
        for (int i=0;i<edges.length;i++){
            if (edges[i] == e){index = i;break;}
        }
        if (index != -1){
            // then remove it (if found)
            LEdge[] nedges = new LEdge[edges.length-1];
            System.arraycopy(edges, 0, nedges, 0, index);
            System.arraycopy(edges, index+1, nedges, index, edges.length-index-1);
            edges = nedges;
        }
        e.tail.removeArc(e);
        e.head.removeArc(e);
    }

    /**@return the actual list used internally, not a copy. Do not temper with (or clone beforehand).*/
    public LNode[] getAllNodes(){
        return nodes;
    }

    /**@return the actual list used internally, not a copy. Do not temper with (or clone beforehand).*/
    public LEdge[] getAllEdges(){
        return edges;
    }

    /**@return the actual list used internally, not a copy. Do not temper with (or clone beforehand).*/
    public LGraph[] getAllGraphs(){
        return graphs;
    }

    /** Get a map of all subgraphs. key = subgraph title, value = instance of LGraph*/
    public HashMap getGraphMap(){
        HashMap res = new HashMap(graphs.length);
        for (LGraph g:graphs){
            res.put(g.getTitle(), g);
        }
        return res;
    }

    public LNode getNode(String title){
        LNode res = null;
        // starting with GV 2.24, edge titles now include port in situations where they did not previously
        // if we manage to find a matching node with port information, then use it
        for (int i=0;i<nodes.length;i++){
            if (nodes[i].title.equals(title)){return nodes[i];}
        }
        // if not, try to find a node matching the title without port information
        if (title.indexOf(LElem.PORT_SEPARATOR) != -1){
            title = title.substring(0, title.indexOf(LElem.PORT_SEPARATOR));
            for (int i=0;i<nodes.length;i++){
                if (nodes[i].title.equals(title)){return nodes[i];}
            }
        }
        // if this also fails, don't return anything
        return null;
    }

    boolean isEmpty(){
        return (nodes.length==0 || edges.length==0);
    }

    public String toString(){
        String res = "";
        for (int i=0;i<nodes.length;i++){
            res += nodes[i].toString() + "\n";
        }
        for (int i=0;i<edges.length;i++){
            res += edges[i].toString() + "\n";
        }
        return res;
    }

    /** Get the logical node corresponding to this glyph.
    *@return null if g is not associated to a logical node.
    */
    public static LNode getNode(Glyph g){
        Object o = (g != null) ? g.getOwner() : null;
        if (o != null){
            return (o instanceof LNode) ? (LNode)o : null;
        }
        return null;
    }

    /** Get the logical arc corresponding to this glyph.
    *@return null if g is not associated to a logical arc.
    */
    public static LEdge getEdge(Glyph g){
        Object o = (g != null) ? g.getOwner() : null;
        if (o != null){
            return (o instanceof LEdge) ? (LEdge)o : null;
        }
        return null;
    }

}
