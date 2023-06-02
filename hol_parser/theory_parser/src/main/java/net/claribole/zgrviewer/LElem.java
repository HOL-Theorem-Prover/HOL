/*   FILE: LNode.java
 *   DATE OF CREATION:  Thu Mar 15 19:18:17 2007
 *   Copyright (c) INRIA, 2007-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: LElem.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import fr.inria.zvtm.glyphs.Glyph;
import fr.inria.zvtm.svg.Metadata;

public class LElem {

    static final String PORT_SEPARATOR = ":";

    String groupID;
    String title;
    // URLs associated with each glyph (there might be different URLs associated with
    // the various glyphs constituting a node or edge)
    String[] URLs;
    String[] tooltips;

    Glyph[] glyphs;

    LElem(){}

    LElem(Metadata md){
        this.groupID = md.getClosestAncestorGroupID();
        this.title = md.getTitle();
        this.URLs = new String[]{md.getURL()};
        this.tooltips = new String[]{md.getURLTitle()};
    }

    public String getTitle(){
        return title;
    }

    public String getURL(Glyph g){
        if (URLs == null){return null;}
        return URLs[0];
    }

    public String getTooltip(Glyph g){
        if (tooltips == null){return null;}
        return tooltips[0];
    }

    public String getGroupID(){
        return groupID;
    }

    public Glyph[] getGlyphs(){
        Glyph[] res = new Glyph[glyphs.length];
        System.arraycopy(glyphs, 0, res, 0, glyphs.length);
        return res;
    }

}
