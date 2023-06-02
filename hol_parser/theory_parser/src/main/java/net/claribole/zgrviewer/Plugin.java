/*   FILE: Plugin.java
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 * $Id: Plugin.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import javax.swing.JFrame;
import java.awt.Image;

import java.util.Hashtable;

/**
 * An interface for ZGRViewer plugins (such as the one based on ZVTM-MPD). See <a href="http://zvtm.sourceforge.net/doc/tutorials/zgrvplugins/index.html">http://zvtm.sourceforge.net/doc/tutorials/zgrvplugins/index.html</a> for more details.
 **/
public interface Plugin {

    /**
     * Set the ZGRViewer instance this plug-in is associated with
     */
    public void setApplication(ZGRViewer app);

    /**
     * Called by ZGRViewer prior to exit (put clean up actions (if any) in here)
     */
    public void terminate();

    /**
     * Called by ZGRViewer at init time when loading preferences from zgrviewer.cfg
     * @param settings contains preferences relevant to this plug-in, as they were exported by method savePreferences
     */
    public void loadPreferences(Hashtable settings);

    /**
     * Called by ZGRViewer when saving preferences to zgrviewer.cfg
     * @return preferences relevant to this plug-in as a hashtable (can be null)
     */
    public Hashtable savePreferences();

    /**
     * Display a window for configuring plugin settings
     **/
    public void showSettings();

    /**
     * Gets author information about this plug-in - return an empty String if none
     **/
    public String getAuthor();

    /**
     * Gets information about this plug-in - return an empty String if none
     **/
    public String getName();

    /**
     * Gets version information about this plug-in - return an empty String if none
     **/
    public String getVersion();

    /**
     * Gets a URL pointing to more information about this plug-in (e.g. Web site) - can be null
     **/
    public java.net.URL getURL();

    /** Does this plugin declare an interaction mode/tool in the toolpalette.
     * @return true if it does
     */
    public boolean hasMode();

    /** Get the icon to be placed in the toolpalette to activate this mode.
     * @return null if no mode associated with this plugin
     */
    public Image getModeIcon();

    /** Callback triggered when the corresponding icon gets selected in the tool palette.
     */
    public void enterMode();

    /** Callback triggered when the corresponding icon gets unselected in the tool palette.
     */
    public void exitMode();

    /** Get the list of built-in modes this plugin would like to disable.
     *@return a list of modes to be disabled. null or an empty array if not disabling any mode.
     */
    public String[] getDisabledModes();

    /** Event triggered when the graph's logical structure has changed. */
    public static final short NOTIFY_PLUGIN_LOGICAL_STRUCTURE_CHANGED = 0;
    /** Event triggered when ZGRViewer's UI has been instantiated and has finished initializing. */
    public static final short NOTIFY_PLUGIN_GUI_INITIALIZED = 1;
    /** Event triggered when ZGRViewer's UI is about to be instantiated. */
    public static final short NOTIFY_PLUGIN_GUI_INITIALIZING = 2;
    /** Event triggered when ZGRViewer's UI has been instantiated but is not yet visible. */
    public static final short NOTIFY_PLUGIN_GUI_VIEW_CREATED = 3;
    /** Event triggered when ZGRViewer's window has been resized. */
    public static final short NOTIFY_PLUGIN_GUI_VIEW_RESIZED = 4;
    /** Event triggered when ZGRViewer has finished loading a file. */
    public static final short NOTIFY_PLUGIN_FILE_LOADED = 5;

    /** Event notification
     *@param event one of NOTIFY_* events
     */
    public void eventOccured(short event);

}

