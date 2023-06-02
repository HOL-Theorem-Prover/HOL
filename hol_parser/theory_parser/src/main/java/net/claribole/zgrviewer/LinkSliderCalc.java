/*   AUTHOR : Tomer Moscovich (tomer@moscovich.net)
 *   Copyright (c) INRIA, 2009-2013. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: LinkSliderCalc.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.geom.AffineTransform;
import java.awt.geom.GeneralPath;
import java.awt.geom.Line2D;
import java.awt.geom.Point2D;
import java.awt.geom.PathIterator;
import java.awt.Point;

import java.util.ArrayList;
import java.util.Iterator;

import fr.inria.zvtm.glyphs.DPath;

/**
 * Given a GeneralPath and a mouse cursor position, calculate path cursor position and scale
 *
 * Usage:
 *    lsc = new LinkSliderCalc(edge.getPathReference(), myViewportWidth));
 *    lsc.updateMousePosition(newMousePos);
 *    patPoint = lsc.getPositionAlongPath();
 *    scale = lsc.getScale();
 */

public class LinkSliderCalc {

    public PolyLine polyLine;

    protected Point2D mousePos;
    protected Point2D nearestPoint;
    protected Line2D nearestSeg;
    protected double viewWidth;
    protected double scale;
    protected double fractionAlongPath;

    DPath path;

    public LinkSliderCalc(DPath p, double viewWidth){
        this(p, 0.5, viewWidth);
    }

    /**
     * @param p         path to slide along
     * @param flatness  optional - min distance between curve control points and flattend polyline representation
     * @param viewWidth width of camera viewport at scale == 1
     */
    public LinkSliderCalc(DPath p, double flatness, double viewWidth){
        this.path = p;
        polyLine = new PolyLine(this.path.getJava2DGeneralPath().getPathIterator(new AffineTransform(), flatness));
        this.viewWidth = viewWidth;
    }

    public DPath getPath(){
        return path;
    }

    /**
     * Call first to set the new mouse position.
     * This calculates the new position and scale factor along the path.
     * @param mousePos
     */
    public void updateMousePosition(Point2D mousePos) {
        this.mousePos = new Point2D.Double(mousePos.getX(), mousePos.getX());

        // Nearest Point and tangent segment
        nearestSeg = polyLine.nearestSegment(mousePos);
        nearestPoint = polyLine.nearestPointOnSegment(mousePos, nearestSeg);

        // Scale
        double partialDist = polyLine.cumLengthAt(nearestPoint);
        double pathLen = polyLine.getLength();

        // connes function
        // in 0..1 unit sqare: y = (1-(x*2-1)^6)^4
        double x = partialDist/pathLen;
        double y = Math.pow(1-Math.pow(x*2-1, 6), 4) * (1-viewWidth/pathLen);
        scale = Math.min(1, Math.max(0.01, 1-y)); // clamp .01 to 1


        // fraction along path
        fractionAlongPath = x;
    }

    /**
     * @return Closest point on curve to mouse position
     * (call updateMousePosition first)
     */
    public Point2D getPositionAlongPath(){
        return nearestPoint;
    }

    /**
     * @return fraction [0..1] closest point is along path
     * (call updateMousePosition first)
     */
    public double getFractionAlongPath(){
        return fractionAlongPath;
    }

    /**
     * @return scale [0.01 to 1] so that viewWidth == path length at midpoint.
     * (call updateMousePosition first)
     */
    public double getScale(){
        return scale;
    }

    /**
     * @return tangent segment to curve at position along path
     * (call updateMousePosition first)
     */
    public Line2D getTangentSegmentAtPathPosition(){
        return nearestSeg;
    }

}

class Vector2D {

    public double x;
    public double y;

    public Vector2D(Point start, Point end){
        x = end.x -  start.x;
        y = end.y -  start.y;
    }
    public Vector2D(Point2D start, Point2D end){
        x = end.getX() -  start.getX();
        y = end.getY() -  start.getY();
    }
    public Vector2D(Vector2D start, Vector2D end){
        x = end.x -  start.x;
        y = end.y -  start.y;
    }

    public Vector2D(Point p){
        x = p.x;
        y = p.y;
    }
    public Vector2D(){
    }
    public Vector2D(double _x, double _y){
        x = _x;
        y = _y;
    }

    public Vector2D(Vector2D v) {
        x = v.x;
        y = v.y;
    }

    public String toString(){
        return "("+(int)x+","+(int)y+")";
    }
    public Vector2D duplicate(){
        return new Vector2D(x,y);
    }

    public static Vector2D normalize(Vector2D v){
        double l = v.length();
        return new Vector2D(v.x/l, v.y/l);
    }
    public void normalize(){
        double l = length();
        x /= l;
        y /= l;
    }

    public void negate(){
        x*=-1;y*=-1;
    }
    public static Vector2D negate(Vector2D v){
        return new Vector2D(-v.x, -v.y);
    }

    public double length(){
        return Math.sqrt(x * x + y * y);
    }

    static public Vector2D add(Vector2D u, Vector2D v){
        return new Vector2D(u.x + v.x, u.y + v.y);
    }
    static public Vector2D add(Vector2D u, Vector2D v, Vector2D w){
        return new Vector2D(u.x + v.x +w.x, u.y + v.y + w.y);
    }
    public void add(Vector2D v){
        x += v.x;   y += v.y;
    }

    static public Vector2D subtract(Point u, Vector2D v){
        return new Vector2D(u.x - v.x, u.y - v.y);
    }
    static public Vector2D subtract(Vector2D u, Vector2D v){
        return new Vector2D(u.x - v.x, u.y - v.y);
    }
    public void subtract(Vector2D v){
        x -= v.x;   y -= v.y;
    }

    static public Vector2D multiply(Vector2D v, double m){
        return new Vector2D(v.x * m, v.y * m);
    }
    public void multiply(double m){
        x *= m; y *= m;
    }

    static public double dot_product(Vector2D u, Vector2D v){
        return u.x * v.x + u.y * v.y;
    }

    static public double cross_product(Vector2D u, Vector2D v){
        return u.x * v.y - u.y * v.x;
    }

    static public double cos(Vector2D u, Vector2D v){
      double length = u.length() * v.length();

      if (length >0)
        return dot_product(u, v) / length;
      else
        return 0;
    }

    static public double sin(Vector2D u, Vector2D v){
      double length = u.length() * v.length();

      if (length >0)
        return (cross_product(u, v)) / length;
      else
        return 0;
    }

    // angle 0 to PI
    public static double get_angle0PI(Vector2D u, Vector2D v){
        double cosine = cos(u, v);
        if (cosine <= -1) return Math.PI;
        else if (cosine >= 1) return 0;
        else return Math.acos(cosine);
    }

    // angle -PI to PI
    public double get_anglePIPI(Vector2D v){
        double cos = cos(this,v);
        double sin = sin(this,v);
        if (cos == 0)
            if (sin > 0)    return Math.PI/2;
            else        return -Math.PI/2;
        if (sin == 0)
            if (cos > 0)    return 0;
            else        return Math.PI;

        // -PI/2   ...   +PI/2
        double angle = Math.atan(sin/cos);

        if (cos < 0)
            if (angle>0)
                angle -= Math.PI;
            else
                angle +=Math.PI;
        return angle;
    }

    public static Vector2D rotate90(Vector2D vec){
        return new Vector2D(vec.y, -vec.x);
    }

    public static Vector2D rotate(Vector2D v, double radians){

        double cos = Math.cos(radians);
        double sin = Math.sin(radians);

        return  new Vector2D(v.x * cos - v.y * sin,
                v.x * sin + v.y * cos );
    }

    public static Vector2D flip(Vector2D vec, Vector2D axis){
        Vector2D x_vec = Vector2D.normalize(axis);

        Vector2D y_vec = Vector2D.rotate90(x_vec);
        double x = Vector2D.dot_product(vec, x_vec);
        double y = Vector2D.dot_product(vec, y_vec);
        y = -y;

        return Vector2D.add(Vector2D.multiply(x_vec, x),
                            Vector2D.multiply(y_vec, y));
    }

    public static double distance(int x1, int y1, int x2, int y2){
      return Math.sqrt((x2-x1)*(x2-x1)+(y2-y1)*(y2-y1));
    }
    public static double distance(Point start, Point end){
      return distance(start.x, start.y, end.x, end.y);
    }
    public static double distance(double x1, double y1, double x2, double y2){
      return Math.sqrt((x2-x1)*(x2-x1)+(y2-y1)*(y2-y1));
    }

    public Point point(){
        return new Point((int)x, (int)y);
    }

    static public Point translatePoint(Point p, Vector2D vec){
        return new Point((int)(p.x+vec.x), (int)(p.y+vec.y));
    }
}

class PolyLine {

    ArrayList<Line2D> segments;     // polyline segments
    ArrayList<Double> cumLengths;   // total length until seg i (exclusive)
    double length;

    public PolyLine(PathIterator pi){
        // get segments
        segments = new ArrayList<Line2D>();
        double[] coords = {0,0,0,0,0,0};
        Point2D lastPt = new Point2D.Double();
        while(!pi.isDone()){
            switch( pi.currentSegment(coords) ) {
                case PathIterator.SEG_MOVETO:
                    lastPt = new Point2D.Double(coords[0], coords[1]);
                    break;
                case PathIterator.SEG_LINETO:
                    Point2D.Double newPt = new Point2D.Double(coords[0], coords[1]);
                    segments.add( new Line2D.Double(lastPt, newPt) );
                    lastPt = newPt;
                    break;
            }
            pi.next();
        }
        // precalc lengths
        calcCumLengths();
    }

    // calculate and store length of each segment
    public void calcCumLengths(){
        length = 0;
        cumLengths = new ArrayList<Double>(segments.size());
        for(int i = 0; i < segments.size(); ++i){
            cumLengths.add(new Double(length));
            length += segmentLength(segments.get(i));
        }
    }
    // cumulative length -- assumes point is on path
    public double cumLengthAt(Point2D pt){
        int segi = nearestSegmentIdx(pt);
        //Point2D nearestPt = nearestPointOnSegment(pt, segments.get(segi));
        Point2D segPt = segments.get(segi).getP1();
        double dx = pt.getX()-segPt.getX();
        double dy = pt.getY()-segPt.getY();
        return cumLengths.get(segi)+ Math.sqrt(dx*dx+dy*dy);
    }
    public double getLength(){
        return length;
    }
    public double getLengthAtSegmentIdx(int idx){
        return cumLengths.get(idx);
    }

    public Point2D nearestPoint(Point2D pt) {
        return nearestPointOnSegment(pt, nearestSegment(pt));
    }

    public Line2D nearestSegment(Point2D pt) {
        return segments.get(nearestSegmentIdx(pt));
    }
    public int nearestSegmentIdx(Point2D pt)
    {
        double shortestDist =java.lang.Double.POSITIVE_INFINITY;
        int nearestSegIdx = 0;
        int i = 0;
        for(i = 0; i < segments.size(); ++i){
            double dist = segments.get(i).ptSegDist(pt);
            if(dist < shortestDist) {
                shortestDist = dist;
                nearestSegIdx = i;
            }
        }
        return nearestSegIdx;
    }


    // Calculate closest point on segment
    public static Point2D nearestPointOnSegment(Point2D pt, Line2D seg){
        Point2D p1 = seg.getP1();
        Point2D p2 = seg.getP2();
        Vector2D segv = new Vector2D(p1, p2);
        double len = segv.length();
        segv.normalize();
        Vector2D ptv = new Vector2D(p1, pt);
        double t = Vector2D.dot_product(ptv, segv)/len;
        Point2D closestPt = p1;
        if(t > 1) {
            closestPt = p2;
        } else if(t > 0) {
            closestPt = new Point2D.Double( (1-t)*p1.getX()+t*p2.getX(),
                                            (1-t)*p1.getY()+t*p2.getY()
                                            );
        }
        return closestPt;

    }
    /*
    public ArrayList<Point2D> getIntersections(PolyLine poly){
        ArrayList<Point2D> intersections = new ArrayList<Point2D>();

        for(int i = 0; i < this.segments.size(); ++i){
            Line2D seg1 = this.segments.get(i);
            for(int j = 0; j < poly.segments.size(); ++j){
                Line2D seg2 = poly.segments.get(j);
                if(seg1.intersectsLine(poly.segments.get(j))){
                    //TODO intersects?  intersections.add(seg1.);
                }

            }

        }

        return intersections;
    }*/
    public static Point2D SegmentSegmentIntersection(Line2D l1, Line2D l2) {
        double x1 = l1.getX1();
        double y1 = l1.getY1();
        double x2 = l1.getX1();
        double y2 = l1.getY2();
        double xx1 = l2.getX1();
        double yy1 = l2.getY1();
        double xx2 = l2.getX2();
        double yy2 = l2.getY2();

        // a * x + b * y + c = 0
        double a0, b0, c0,  a1, b1, c1;
        a0 = y1 - y2;
        b0 = x2 - x1;
        c0 = y2 * x1 - x2 * y1;
        a1 = yy1 - yy2;
        b1 = xx2 - xx1;
        c1 = yy2 * xx1 - xx2 * yy1;

        if (Math.abs(a0 * b1 - a1 * b0) < 0.00001){
             return null;
        }

        double x = ((b0 * c1 - b1 * c0)/(a0 * b1 - a1 * b0)) ;
        double y = ((a0 * c1 - a1 * c0)/(a1 * b0 - a0 * b1));
        return new Point2D.Double(x,y);

    }

    // Calculate the intersection of a ray and a circle
    // Segment seg, circle center at cc, radius r
    // Zero to two intersections are returned  in int1, int 2
    // Return FALSE if no intersection
    public boolean rayCircleIntersections(Line2D seg,Point2D cc,double r, Point2D int1, Point2D int2)
    {
       Point2D p1 = seg.getP1();
       Point2D p2 = seg.getP2();
       double mu1, mu2;
       double a,b,c;
       double bb4ac;
       Point2D.Double dp;

       dp = new Point2D.Double( p2.getX() - p1.getX(), p2.getY() - p1.getY());

       a = dp.getX() * dp.getX() + dp.getY() * dp.getY();
       b = 2 * (dp.getX() * (p1.getX() - cc.getX()) + dp.getY() * (p1.getY() - cc.getY()));
       c = cc.getX() * cc.getX() + cc.getY() * cc.getY();
       c += p1.getX() * p1.getX() + p1.getY() * p1.getY();
       c -= 2 * (cc.getX() * p1.getX() + cc.getY() * p1.getY());
       c -= r * r;
       bb4ac = b * b - 4 * a * c;
       if (Math.abs(a) < 0.00001 || bb4ac < 0) {
          int1.setLocation(Double.NaN, Double.NaN);
          int2.setLocation(Double.NaN, Double.NaN);
          return false;
       }

       mu1 = (-b + Math.sqrt(bb4ac)) / (2 * a);
       mu2 = (-b - Math.sqrt(bb4ac)) / (2 * a);
       Vector2D v1 = new Vector2D(p1, p2);
       Vector2D v2 = new Vector2D(p1, p2);
       v1.multiply(mu1);
       v2.multiply(mu2);
       int1.setLocation(p1.getX()+v1.x, p1.getY()+v1.y);
       int2.setLocation(p2.getX()+v2.x, p2.getY()+v1.y);
       return true;
    }
    // finds an intersection with a circle of radius r, centered on point 0.
    // if found, returns index of intersecting segment, and places intersection pt in intPt
    // if no intersection is found, a new radius is calculated: altR * distance between endpoints
    // if something is wrong, returns -1;
    public int intersectsCircleOnStartPoint(double r, double altR,  Point2D intPt)
    {
        Point2D center = segments.get(0).getP1();
        Point2D pt1 = new Point2D.Double();
        Point2D pt2 = new Point2D.Double();
        for(int i = 0; i < segments.size(); ++i){
            if(center.distance(segments.get(i).getP2()) < r) { continue; }
            if( rayCircleIntersections(segments.get(i), center, r, pt1, pt2) ) {
                intPt.setLocation(pt1);
                return i;
            }
        }
        // No intersection, calc new r
        Double shortR = altR * center.distance(segments.get(segments.size()-1).getP2());
        for(int i = 0; i < segments.size(); ++i){
            if(center.distance(segments.get(i).getP2()) < shortR) { continue; }
            if( rayCircleIntersections(segments.get(i), center, shortR, pt1, pt2) ) {
                intPt.setLocation(pt1);
                return i;
            }
        }
        return -1;

    }

    public static final double segmentLength(Line2D seg){
        double dx = seg.getX2()-seg.getX1();
        double dy = seg.getY2()-seg.getY1();
        return Math.sqrt(dx*dx + dy*dy);
    }

    public Point2D firstPoint() {
        return segments.get(0).getP1();
    }
    public Point2D lastPoint() {
        return segments.get(segments.size()-1).getP2();
    }
}
