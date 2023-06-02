/*   FILE: Utils.java
 *   DATE OF CREATION:   Thu Jan 09 14:14:35 2003
 *   Copyright (c) Emmanuel Pietriga, 2002-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 *$Id: AppletUtils.java 4936 2013-02-21 13:55:55Z epietrig $
 */

package net.claribole.zgrviewer;

import java.awt.Font;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;

import javax.swing.UIManager;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.FactoryConfigurationError;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.xml.sax.SAXException;


public class AppletUtils {

    static Font smallFont=new Font("Dialog",0,10);
    static java.awt.Color pastelBlue=new java.awt.Color(156,154,206);
    static java.awt.Color darkerPastelBlue=new java.awt.Color(125,123,165);

//     private static final String mac="com.sun.java.swing.plaf.mac.MacLookAndFeel";
//     private static final String metal="javax.swing.plaf.metal.MetalLookAndFeel";
//     private static final String motif="com.sun.java.swing.plaf.windows.WindowsLookAndFeel";
//     private static String currentLookAndFeel="com.sun.java.swing.plaf.motif.MotifLookAndFeel";

    public static void initLookAndFeel(){
//  try {UIManager.setLookAndFeel(currentLookAndFeel);}
//  catch(Exception ex){System.err.println("An error occured while trying to change the look and feel\n"+ex);}
    String key;
    Object okey;
    for (Enumeration e=UIManager.getLookAndFeelDefaults().keys();e.hasMoreElements();){
        okey = e.nextElement(); // depending on JVM (1.5.x and earlier, or 1.6.x or later) and OS,
        key = okey.toString();  // keys are respectively String or StringBuffer objects
        if (key.endsWith(".font") || key.endsWith("Font")){UIManager.put(okey, smallFont);}
    }
    UIManager.put("ProgressBar.foreground",pastelBlue);
    UIManager.put("ProgressBar.background",java.awt.Color.lightGray);
    UIManager.put("Label.foreground",java.awt.Color.black);
    }

    /**
     * tells whether the underlying OS is Windows (Win32) or not
     */
    public static boolean osIsWindows(){
    return fr.inria.zvtm.engine.Utils.osIsWindows();
    }

    /**
     * tells whether the underlying OS is Mac OS X or not
     */
    public static boolean osIsMacOS(){
    return fr.inria.zvtm.engine.Utils.osIsMacOS();
    }

    /**
     * tells wheter the current JVM is version 1.4.0 and later (or not)
     */
    public static boolean javaVersionIs140OrLater(){
    String version=System.getProperty("java.vm.version");
    float numVer=(new Float(version.substring(0,3))).floatValue();
    if (numVer>=1.4f){return true;}
    else {return false;}
    }

    /**
     * Create a File object from the given directory and file names
     *
     *@param directory the file's directory
     *@param prefix the file's prefix name (not its directory)
     *@param suffix the file's suffix or extension name
     *@return a File object if a temporary file is created; null otherwise
     */
    public static File createTempFile (String directory, String prefix, String suffix){
        File f;
        try {
            File d=new File(directory);
            f=File.createTempFile(prefix,suffix,d);
        }
    catch (Exception e){e.printStackTrace();return null;}
        return f;
    }

    public static Document parse(File f,boolean validation){ 
    try {
        DocumentBuilderFactory factory=DocumentBuilderFactory.newInstance();
        factory.setValidating(validation);
        if (!validation){factory.setAttribute("http://apache.org/xml/features/nonvalidating/load-external-dtd",new Boolean(false));}
        factory.setNamespaceAware(true);
        DocumentBuilder builder=factory.newDocumentBuilder();
        Document res=builder.parse(f);
        return res;
    }
    catch (FactoryConfigurationError e){e.printStackTrace();return null;} 
    catch (ParserConfigurationException e){e.printStackTrace();return null;}
    catch (SAXException e){e.printStackTrace();return null;}
    catch (IOException e){e.printStackTrace();return null;}
    }

    public static Document parse(InputStream is,boolean validation){ 
    try {
        DocumentBuilderFactory factory=DocumentBuilderFactory.newInstance();
        factory.setValidating(validation);
        if (!validation){factory.setAttribute("http://apache.org/xml/features/nonvalidating/load-external-dtd",new Boolean(false));}
        factory.setNamespaceAware(true);
        DocumentBuilder builder=factory.newDocumentBuilder();
        Document res=builder.parse(is);
        return res;
    }
    catch (FactoryConfigurationError e){e.printStackTrace();return null;} 
    catch (ParserConfigurationException e){e.printStackTrace();return null;}
    catch (SAXException e){e.printStackTrace();return null;}
    catch (IOException e){e.printStackTrace();return null;}
    }

    public static Document parse(String uri,boolean validation){ 
    try {
        DocumentBuilderFactory factory=DocumentBuilderFactory.newInstance();
        factory.setValidating(validation);
        if (!validation){factory.setAttribute("http://apache.org/xml/features/nonvalidating/load-external-dtd",new Boolean(false));}
        factory.setNamespaceAware(true);
        DocumentBuilder builder=factory.newDocumentBuilder();
        Document res=builder.parse(uri);
        return res;
    }
    catch (FactoryConfigurationError e){e.printStackTrace();return null;} 
    catch (ParserConfigurationException e){e.printStackTrace();return null;}
    catch (SAXException e){e.printStackTrace();return null;}
    catch (IOException e){e.printStackTrace();return null;}
    }

//     public static void serialize(Document d,File f){
//  OutputFormat format=new OutputFormat(d,"UTF-8",true);
//      format.setLineSeparator(LineSeparator.Web);
//  try {
//      XMLSerializer serializer=new XMLSerializer(new FileWriter(f.toString()),format);
//      serializer.asDOMSerializer();
//      serializer.serialize(d);
//  }
//  catch (IOException e){e.printStackTrace();}
//     }

    /**increment a byte representing a char value with the following values (in order) 0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0*/
    public static byte incByte(byte b){
    byte res;
    if (b<0x7a){
        if (b==0x39){res=0x41;}
        else if (b==0x5a){res=0x61;}
        else {res=++b;}
    }
    else {res=0x30;}
    return res;
    }

    /**
     *Replaces all occurences of key in input by replacement
     */
    public static String replaceString(String input, String key, String replacement) {
        String res="";
        int keyLength=key.length();
        int index=input.indexOf(key);
        int lastIndex=0;
        while (index>=0) {
            res=res+input.substring(lastIndex,index)+replacement;
            lastIndex=index+keyLength;
            index=input.indexOf(key,lastIndex);
        }
    res+=input.substring(lastIndex,input.length());
        return res;
    }

    public static String rankString(int number){
    String res = Integer.toString(number);
    if (res.endsWith("1")){return (res.endsWith("11")) ? res + "th" : res + "st";}
    else if (res.endsWith("2")){return (res.endsWith("12")) ? res + "th" : res + "nd";}
    else if (res.endsWith("3")){return (res.endsWith("13")) ? res + "th" : res + "rd";}
    else {return res + "th";}
    }

    public static String join(String[] strings, String sep){
    if (strings.length > 0){
        String res = strings[0];
        for (int i=1;i<strings.length;i++){
        res += sep + strings[i];
        }
        return res;
    }
    else {
        return "";
    }
    }

}
