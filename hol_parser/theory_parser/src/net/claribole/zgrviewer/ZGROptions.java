/*   Copyright (c) INRIA, 2015. All Rights Reserved
 * $Id: ZGROptions.java 5326 2015-02-05 21:25:41Z epietrig $
 */

package net.claribole.zgrviewer;

import java.util.ArrayList;
import java.util.List;

import org.kohsuke.args4j.Argument;
import org.kohsuke.args4j.Option;

public class ZGROptions {

    @Option(name = "-bw", aliases = {"--block-width"}, usage = "clustered view block width")
    public int blockWidth = 400;

    @Option(name = "-bh", aliases = {"--block-height"}, usage = "clustered view block height")
    public int blockHeight = 300;

    @Option(name = "-r", aliases = {"--num-rows"}, usage = "number of rows in the clustered view")
    public int numRows = 2;

    @Option(name = "-c", aliases = {"--num-cols"}, usage = "number of columns in the clustered view")
    public int numCols = 2;

    @Option(name = "-mw", aliases = {"--mullion-width"}, usage = "mullions width")
    public int mullionWidth = 0;

    @Option(name = "-mh", aliases = {"--mullion-height"}, usage = "mullions height")
    public int mullionHeight = 0;

    @Option(name = "-f", aliases = {"--gv-file"}, usage = "GraphViz file to display")
    public String gvFile = null;

    @Option(name = "-P", aliases = {"--gv-program"}, usage = "GraphViz program used to compute the layout: one of dot, neato, twopi, circo, svg")
    public String cmdLinePrg = null;

    @Option(name = "-plgDir", aliases = {"--plugin-dir"}, usage = "Directory where to look for ZGRViewer plugins")
    public String pluginDir = null;

    @Option(name = "-plgList", aliases = {"--plugin-list"}, usage = "List of paths to specific JAR files where to look for ZGRViewer plugins. Overrides -plgDir")
    public String pluginList = null;

    @Option(name = "-plgMode", aliases = {"--plugin-mode"}, usage = "Plugin mode enabled by default in tool palette. Give the class name corresponding to the plugin.")
    public String pluginMode = null;

    @Option(name = "-fs", aliases = {"--fullscreen"}, usage = "full-screen")
    public boolean fullscreen = false;

    @Option(name = "-ogl", aliases = {"--opengl"}, usage = "enable Java2D OpenGL rendering")
    public boolean opengl = false;

    @Argument
    List<String> arguments = new ArrayList<String>();

    public boolean standalone = true; //not a CLI option

}


