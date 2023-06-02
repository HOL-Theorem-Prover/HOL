/*   FILE: ZGRViewer.java
 *   DATE OF CREATION:   Wed Aug 30 12:02:31 2006
 *   Copyright (c) INRIA, 2006-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 *   $Id: ToolPalette.java 4943 2013-02-21 17:49:54Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Cursor;
import java.awt.BasicStroke;
import java.awt.geom.Point2D;
import javax.swing.ImageIcon;

import java.util.Vector;
import java.util.HashMap;

import fr.inria.zvtm.engine.Camera;
import fr.inria.zvtm.engine.VirtualSpace;
import fr.inria.zvtm.engine.View;
import fr.inria.zvtm.glyphs.VImage;
import fr.inria.zvtm.animation.Animation;
import fr.inria.zvtm.animation.interpolation.SlowInSlowOutInterpolator;

public class ToolPalette {

    GraphicsManager grMngr;

    static final String PALETTE_SPACE_NAME = "tps";
    VirtualSpace paletteSpace;
    Camera paletteCamera;

    public static final String PLUGIN_MODE_PREFIX = "plugin";

    static final String TOOLPALETTE_BUTTON = "tpb";

    public static final String STD_NAV_MODE = "st";
    public static final String FL_NAV_MODE = "fl";
    public static final String DM_NAV_MODE = "dm";
    public static final String PL_NAV_MODE = "pl";
    public static final String HIGHLIGHT_MODE = "hi";
    public static final String BRING_AND_GO_MODE = "bg";
    public static final String LINK_SLIDING_MODE = "ls";
    public static final String EDIT_MODE = "ed";

    static final String[] BUILTIN_MODES = {STD_NAV_MODE, FL_NAV_MODE, DM_NAV_MODE, PL_NAV_MODE,
                                           HIGHLIGHT_MODE, BRING_AND_GO_MODE, LINK_SLIDING_MODE, EDIT_MODE};

    static final HashMap<String,String> BUILTIN_MODE_ICON_PATHS = new HashMap(8);
    static {
        BUILTIN_MODE_ICON_PATHS.put(STD_NAV_MODE,"/images/stdnav24b.png");
        BUILTIN_MODE_ICON_PATHS.put(FL_NAV_MODE,"/images/flnav24b.png");
        BUILTIN_MODE_ICON_PATHS.put(DM_NAV_MODE,"/images/dmnav24b.png");
        BUILTIN_MODE_ICON_PATHS.put(PL_NAV_MODE,"/images/plnav24b.png");
        BUILTIN_MODE_ICON_PATHS.put(HIGHLIGHT_MODE,"/images/hl24b.png");
        BUILTIN_MODE_ICON_PATHS.put(BRING_AND_GO_MODE,"/images/fl24b.png");
        BUILTIN_MODE_ICON_PATHS.put(LINK_SLIDING_MODE,"/images/ls24b.png");
        BUILTIN_MODE_ICON_PATHS.put(EDIT_MODE,"/images/edit24b.png");
    };

    VImage[] buttons;
    VImage[] selectedButtons;
    static final int VERTICAL_STEP_BETWEEN_ICONS = 30;

    VImage currentModeIcon = null;
    String currentMode = null;

    boolean visible = false;
    boolean paintPalette = true; // set to false temporarily during panel resizing operations ; used as an optimization indicator
    boolean enabled = true;

    public static final int ANIM_TIME = 200;
    public static final int TRIGGER_ZONE_WIDTH = 48;
    public static int TRIGGER_ZONE_HEIGHT = BUILTIN_MODES.length * (VERTICAL_STEP_BETWEEN_ICONS) + 24;

    short firstPluginModeIndex = -1;

    ToolPalette(GraphicsManager gm){
        this.grMngr = gm;
        loadBuiltinModes();
        loadPluginModes();
        // update original trigger zone height
        TRIGGER_ZONE_HEIGHT = buttons.length * (VERTICAL_STEP_BETWEEN_ICONS) + 24;
        selectDefaultMode();
    }

    void loadBuiltinModes(){
        paletteSpace = grMngr.vsm.addVirtualSpace(PALETTE_SPACE_NAME);
        paletteCamera = paletteSpace.addCamera();
        paletteCamera.setAltitude(0);
        // building list of built-in modes that plugins want to disable
        Plugin[] plugins = grMngr.cfgMngr.plugins;
        HashMap<String,Object> modesToDisable = new HashMap(2);
        if (plugins != null){
            for (short i=0;i<plugins.length;i++){
                String[] mtd = plugins[i].getDisabledModes();
                if (mtd != null && mtd.length > 0){
                    for (String bimode:mtd){
                        modesToDisable.put(bimode, null);
                    }
                }
            }
        }
        // instantiating remaining built-in modes
        buttons = new VImage[BUILTIN_MODES.length-modesToDisable.size()];
        short i = 0;
        short j = 0;
        while (i < BUILTIN_MODES.length){
            if (modesToDisable.containsKey(BUILTIN_MODES[i])){}
            else {
                buttons[j] = new VImage(0, -j*VERTICAL_STEP_BETWEEN_ICONS, 0,
                    (new ImageIcon(this.getClass().getResource(BUILTIN_MODE_ICON_PATHS.get(BUILTIN_MODES[i])))).getImage());
                paletteSpace.addGlyph(buttons[j]);
                buttons[j].setOwner(BUILTIN_MODES[i]);
                buttons[j].setType(TOOLPALETTE_BUTTON);
                j++;
            }
            i++;
        }
        firstPluginModeIndex = j;
    }

    void selectDefaultMode(){
        if (defaultPluginModeClassName != null && pluginsWithMode != null && pluginsWithMode.size() > 0){
            for (Short index:pluginsWithMode.keySet()){
                Plugin p = pluginsWithMode.get(index);
                if (p.getClass().getName().equals(defaultPluginModeClassName)){
                    selectMode(buttons[index.shortValue()]);
                    return;
                }
            }
        }
        selectMode(buttons[0]);
    }

    public void setEnabled(boolean b){
        enabled = b;
        paletteCamera.setEnabled(b);
    }

    public boolean isEnabled(){
        return enabled;
    }

    public boolean isStdNavMode(){
        return currentMode.equals(STD_NAV_MODE);
    }

    public boolean isFadingLensNavMode(){
        return currentMode.equals(FL_NAV_MODE);
    }

    public boolean isDragMagNavMode(){
        return currentMode.equals(DM_NAV_MODE);
    }

    public boolean isProbingLensNavMode(){
        return currentMode.equals(PL_NAV_MODE);
    }

    public boolean isHighlightMode(){
        return currentMode.equals(HIGHLIGHT_MODE);
    }

    public boolean isBringAndGoMode(){
        return currentMode.equals(BRING_AND_GO_MODE);
    }

    public boolean isLinkSlidingMode(){
        return currentMode.equals(LINK_SLIDING_MODE);
    }

    public boolean isEditMode(){
        return currentMode.equals(EDIT_MODE);
    }

    public String getMode(){
        return currentMode;
    }

    static final BasicStroke SB_STROKE = new BasicStroke(2f);
    static final BasicStroke DB_STROKE = new BasicStroke(1f);

    public void selectMode(VImage icon){
        boolean newModeSelected = false;
        String previousMode = currentMode;
        if (icon != currentModeIcon){
            if (currentModeIcon != null){
                // remove thick border from previously selected icon
                currentModeIcon.setStroke(DB_STROKE);
            }
            currentModeIcon = icon;
            // add thick border to newly selected icon
            currentModeIcon.setStroke(SB_STROKE);
            currentMode = (String)icon.getOwner();
            newModeSelected = true;
        }
        if (newModeSelected && previousMode != null){
            // if a new button has been selected,
            // discard resources associated with old mode
            if (previousMode.equals(DM_NAV_MODE)){
                grMngr.killDM();
            }
            else if (previousMode.equals(BRING_AND_GO_MODE)){
                grMngr.exitBringAndGoMode();
            }
            else if (previousMode.equals(STD_NAV_MODE)){
                grMngr.activateDynaSpot(false, false);
            }
            else if (previousMode.equals(EDIT_MODE)){
                grMngr.geom.clearSplineEditingGlyphs();
            }
            // init new mode
            if (currentMode.equals(BRING_AND_GO_MODE)){
                grMngr.enterBringAndGoMode();
            }
            else if (currentMode.equals(STD_NAV_MODE)){
                if (ConfigManager.DYNASPOT){
                    try {grMngr.activateDynaSpot(true, false);}
                    catch (NullPointerException ex){}
                }
            }
            // callbacks
            if (previousMode.startsWith(PLUGIN_MODE_PREFIX)){
                // a plugin mode, notify the plugin
                getPlugin(Short.parseShort(previousMode.substring(PLUGIN_MODE_PREFIX.length()))).exitMode();
            }
            if (currentMode.startsWith(PLUGIN_MODE_PREFIX)){
                // a plugin mode, notify the plugin
                getPlugin(Short.parseShort(currentMode.substring(PLUGIN_MODE_PREFIX.length()))).enterMode();
            }
        }
    }

    /* Called with false when resizing the main view to temporarily hide the palette
       until it actually gets relocated to the top-left corner of that window.
       It is then called with true.*/
    public void displayPalette(boolean b){
        if (paintPalette == b){return;}
        for (int i=0;i<buttons.length;i++){
            buttons[i].setVisible(b);
        }
        paintPalette = b;
    }

    public void updateHiddenPosition(){
        double[] wnes = grMngr.mainView.getVisibleRegion(paletteCamera);
        for (int i=0;i<buttons.length;i++){
            buttons[i].moveTo(wnes[0]-buttons[i].getWidth()/2+1, wnes[1]-(i+1)*VERTICAL_STEP_BETWEEN_ICONS);
        }
        displayPalette(true);
    }

    public void show(){
        if (!visible){
            visible = true;
            Animation a = grMngr.vsm.getAnimationManager().getAnimationFactory().createCameraTranslation(ANIM_TIME, paletteCamera,
                new Point2D.Double(-buttons[0].getWidth()-2, 0), true,
                SlowInSlowOutInterpolator.getInstance(), null);
            grMngr.vsm.getAnimationManager().startAnimation(a, false);
            grMngr.mainView.setCursorIcon(Cursor.HAND_CURSOR);
            grMngr.mainView.setActiveLayer(2);
        }
    }

    public void hide(){
        if (visible){
            visible = false;
            Animation a = grMngr.vsm.getAnimationManager().getAnimationFactory().createCameraTranslation(ANIM_TIME, paletteCamera,
                new Point2D.Double(buttons[0].getWidth()+2, 0), true,
                SlowInSlowOutInterpolator.getInstance(), null);
            grMngr.vsm.getAnimationManager().startAnimation(a, false);
            grMngr.mainView.setCursorIcon(Cursor.CUSTOM_CURSOR);
            grMngr.mainView.setActiveLayer(0);
        }
    }

    /**
     * return false if palette is temporarily disabled
     */
    public boolean insidePaletteTriggerZone(int jpx, int jpy){
        return (paintPalette && jpx < TRIGGER_ZONE_WIDTH && jpy < TRIGGER_ZONE_HEIGHT);
    }

    public boolean isShowing(){
    return visible;
    }

    public Camera getPaletteCamera(){
    return paletteCamera;
    }

    //public void showLogicalTools(){
    //    for (int i=4;i<=6;i++){
    //        if (!buttons[i].isSensitive()){buttons[i].setSensitivity(true);}
    //        if (!buttons[i].isVisible()){buttons[i].setVisible(true);}
    //    }
    //}
    //
    //public void hideLogicalTools(){
    //  if (isHighlightMode() || isBringAndGoMode() || isLinkSlidingMode()){
    //      // if a tool that makes needs to know about the logical structure is selected,
    //      // select something else as they are about to be disabled
    //      selectButton(buttons[0]);
    //  }
    //  for (int i=4;i<=6;i++){
    //      if (buttons[i].isSensitive()){buttons[i].setSensitivity(false);}
    //      if (buttons[i].isVisible()){buttons[i].setVisible(false);}
    //  }
    //}

    /* ---------------- plugin modes ------------------*/

    static String defaultPluginModeClassName = null;
    static void setDefaultPluginMode(String pluginClassName){
        defaultPluginModeClassName = pluginClassName;
    }

    HashMap<Short,Plugin> pluginsWithMode;

    void loadPluginModes(){
        Plugin[] plugins = grMngr.cfgMngr.plugins;
        if (plugins == null){return;}
        Vector<Plugin> pwm = new Vector<Plugin>(plugins.length);
        for (int i=0;i<plugins.length;i++){
            if (plugins[i].hasMode()){
                pwm.add(plugins[i]);
            }
        }
        if (pwm.isEmpty()){return;}
        pluginsWithMode = new HashMap<Short,Plugin>(pwm.size());
        VImage[] nbuttons = new VImage[buttons.length+pwm.size()];
        System.arraycopy(buttons, 0, nbuttons, 0, buttons.length);
        buttons = nbuttons;
        for (int i=firstPluginModeIndex;i<firstPluginModeIndex+pwm.size();i++){
            Plugin p = pwm.elementAt(i-firstPluginModeIndex);
            pluginsWithMode.put(new Short((short)i), p);
            buttons[i] = new VImage(0, -i*VERTICAL_STEP_BETWEEN_ICONS, 0, p.getModeIcon());
            buttons[i].setOwner(PLUGIN_MODE_PREFIX+String.valueOf(i));
            buttons[i].setType(TOOLPALETTE_BUTTON);
            paletteSpace.addGlyph(buttons[i]);
        }
    }

    Plugin getPlugin(short index){
        return pluginsWithMode.get(new Short(index));
    }

}
