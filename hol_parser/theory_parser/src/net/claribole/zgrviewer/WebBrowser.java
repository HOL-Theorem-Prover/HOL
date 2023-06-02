/*   FILE: WebBrowser.java
 *   DATE OF CREATION:   Wed Dec 03 09:11:41 2003
 *   Copyright (c) Emmanuel Pietriga, 2002. All Rights Reserved
 *   Copyright (c) INRIA, 2004-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *   $Id: WebBrowser.java 4942 2013-02-21 17:26:22Z epietrig $
 */

package net.claribole.zgrviewer;

import java.io.IOException;

class WebBrowser {

    WebBrowser(){}

    public void show(String url, GraphicsManager gm){
    if (url!=null && url.length()>0){   //perhaps we should try to convert it to a URL, or make the param a URL
        String command=null;            //instead of a string
        if (ConfigManager.autoDetectBrowser){  //try to autodetect browser
        try {
            if (Utils.osIsWindows()){//running under Win32
            command="rundll32 url.dll,FileProtocolHandler "+url;
            Process proc=Runtime.getRuntime().exec(command);
            }
            else if (Utils.osIsMacOS()){
            command = "open "+url;
            Process proc=Runtime.getRuntime().exec(command);
            }
            else {//UNIX and perhaps Linux - not tested yet  (no support for Mac right now)
            command="mozilla-firefox -remote openURL("+url+")";
            Process proc=Runtime.getRuntime().exec(command);
            int exitCode;
            try {
                if ((exitCode=proc.waitFor())!=0){
                command="mozilla-firefox "+url;
                proc=Runtime.getRuntime().exec(command);
                }
            }
            catch (InterruptedException ex1){javax.swing.JOptionPane.showMessageDialog(gm.vsm.getActiveView().getFrame(),"Browser invocation failed "+command+"\n"+ex1);}
            }

        }
        catch (IOException ex2){javax.swing.JOptionPane.showMessageDialog(gm.vsm.getActiveView().getFrame(),"Browser invocation failed "+command+"\n"+ex2);}
        }
        else {
        try {
            command=ConfigManager.browserPath+" "+ConfigManager.browserOptions+" "+url;
            Process proc=Runtime.getRuntime().exec(command);
        }
        catch (Exception ex3){javax.swing.JOptionPane.showMessageDialog(gm.vsm.getActiveView().getFrame(),"Browser invocation failed "+command+"\n"+ex3);}
        }
    }
    }

}
