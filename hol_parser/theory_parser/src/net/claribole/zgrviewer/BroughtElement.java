/*   FILE: LNode.java
 *   Copyright (c) INRIA, 2008-2010. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: BroughtElement.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import fr.inria.zvtm.engine.VirtualSpaceManager;
import fr.inria.zvtm.animation.AnimationManager;
import fr.inria.zvtm.animation.Animation;
import fr.inria.zvtm.animation.EndAction;
import fr.inria.zvtm.animation.interpolation.SlowInSlowOutInterpolator;
import fr.inria.zvtm.animation.interpolation.IdentityInterpolator;
import java.awt.geom.Point2D;
import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.glyphs.VText;
import fr.inria.zvtm.glyphs.DPath;

abstract class BroughtElement {

    static BroughtElement rememberPreviousState(LElem el){
        if (el instanceof LNode){return new BroughtNode((LNode)el);}
        else if (el instanceof LEdge){return new BroughtEdge((LEdge)el);}
        else {return null;}
    }

    Glyph[] glyphs;
    Point2D.Double[] previousLocations;

    abstract Point2D.Double restorePreviousState(int duration, Glyph g);

}

class BroughtNode extends BroughtElement {

    double[] previousSize;

    BroughtNode(LNode n){
        glyphs = n.getGlyphs();
        previousLocations = new Point2D.Double[glyphs.length];
        previousSize = new double[glyphs.length];
        for (int i=0;i<glyphs.length;i++){
            previousLocations[i] = glyphs[i].getLocation();
            previousSize[i] = (glyphs[i] instanceof VText) ? ((VText)glyphs[i]).getScale() : glyphs[i].getSize();
        }
    }

    Point2D.Double restorePreviousState(int duration, Glyph g){
        for (int i=0;i<glyphs.length;i++){
            if (glyphs[i] instanceof VText){
                final VText t = (VText)glyphs[i];
                final double sz = previousSize[i];
                Animation a = VirtualSpaceManager.INSTANCE.getAnimationManager().getAnimationFactory().createGlyphTranslation(
                    duration, glyphs[i], previousLocations[i], false, SlowInSlowOutInterpolator.getInstance(),
                    new EndAction(){
                        public void execute(Object subject, Animation.Dimension dimension){
                            t.setScale((float)sz);
                        }
                    }
                );
                VirtualSpaceManager.INSTANCE.getAnimationManager().startAnimation(a, true);
            }
            else {
                Animation a = VirtualSpaceManager.INSTANCE.getAnimationManager().getAnimationFactory().createGlyphTranslation(
                    duration, glyphs[i], previousLocations[i], false, SlowInSlowOutInterpolator.getInstance(), null);
                VirtualSpaceManager.INSTANCE.getAnimationManager().startAnimation(a, true);
                if (previousSize[i] != glyphs[i].getSize()){
                    a = VirtualSpaceManager.INSTANCE.getAnimationManager().getAnimationFactory().createGlyphSizeAnim(
                        duration, glyphs[i], previousSize[i], false, SlowInSlowOutInterpolator.getInstance(), null);
                    VirtualSpaceManager.INSTANCE.getAnimationManager().startAnimation(a, true);
                }
            }
        }
        int i = fr.inria.zvtm.engine.Utils.indexOfGlyph(glyphs, g);
        return (i != -1) ? previousLocations[i] : null;
    }

}

class BroughtEdge extends BroughtElement {

    DPath spline;
    float splineAlpha;
    Point2D.Double[] splineCoords;

    BroughtEdge(LEdge e){
        glyphs = e.getGlyphs();
        spline = e.getSpline();
        if (spline != null){
            splineCoords = spline.getAllPointsCoordinates();
            splineAlpha = spline.getTranslucencyValue();
        }
        previousLocations = new Point2D.Double[glyphs.length];
        for (int i=0;i<glyphs.length;i++){
            if (glyphs[i] == spline){
                previousLocations[i] = null;
            }
            else if (glyphs[i] instanceof VText){
                previousLocations[i] = glyphs[i].getLocation();
            }
            else {
                // probably a tail or head decoration, we've just hidden the glyph, don't do anything
                previousLocations[i] = null;
            }
        }
    }

    Point2D.Double restorePreviousState(int duration, Glyph g){
        Animation a = VirtualSpaceManager.INSTANCE.getAnimationManager().getAnimationFactory().createPathAnim(
            duration, spline, splineCoords,
            false, SlowInSlowOutInterpolator.getInstance(), null);
        VirtualSpaceManager.INSTANCE.getAnimationManager().startAnimation(a, true);
        spline.setTranslucencyValue(splineAlpha);
        for (int i=0;i<glyphs.length;i++){
            if (!glyphs[i].isVisible()){
                glyphs[i].setVisible(true);
            }
            if (previousLocations[i] != null){
                a = VirtualSpaceManager.INSTANCE.getAnimationManager().getAnimationFactory().createGlyphTranslation(
                    duration, glyphs[i], previousLocations[i], false, SlowInSlowOutInterpolator.getInstance(), null);
                VirtualSpaceManager.INSTANCE.getAnimationManager().startAnimation(a, true);
            }
        }
        return null;
    }

}
