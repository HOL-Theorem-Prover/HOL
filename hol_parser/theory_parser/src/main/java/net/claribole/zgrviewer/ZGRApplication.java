/*   FILE: StatusBar.java
 *   DATE OF CREATION:   Thu Nov 30 11:29:31 2006
 *   Copyright (c) INRIA, 2006-2011. All Rights Reserved
 *   Licensed under the GNU LGPL. For full terms see the file COPYING.
 *
 *   $Id: ZGRApplication.java 4961 2013-05-30 20:39:29Z epietrig $
 */

package net.claribole.zgrviewer;

public interface ZGRApplication {

    public void about();

    public void setStatusBarText(String s);

    public boolean exitVMonClose();

}
